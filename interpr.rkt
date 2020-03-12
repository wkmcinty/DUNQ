#lang typed/racket
(require typed/rackunit)

(define-type ExprC (U numC idC appC ifC lamC stringC recC setC))
(struct numC ([n : Real])#:transparent)
(struct idC ([id : Symbol])#:transparent)
(struct stringC ([s : String])#:transparent)
(struct appC ([fun : ExprC] [args : (Listof ExprC)])#:transparent)
(struct ifC ([x : ExprC] [then : ExprC] [else : ExprC])#:transparent)
(struct lamC ([args : (Listof Symbol)] [argsT : (Listof Ty)] [body : ExprC])#:transparent)
(struct recC ([rname : Symbol] [rbody : lamC] [rretT : Ty] [mbody : ExprC]))
(struct setC ([var : Symbol] [val : ExprC])#:transparent)

(define-type Value (U numV boolV closV primopV stringV nullV))
(struct numV ([n : Real])#:transparent)
(struct boolV ([b : Boolean])#:transparent)
(struct stringV ([s : String])#:transparent)
(struct closV ([args : (Listof Symbol)] [body : ExprC] [env : Env])#:transparent)
(struct primopV ([op : (-> (Listof Value) Value)])#:transparent)
(struct nullV ()#:transparent)

(define-type Ty (U numT boolT strT funT))
(struct numT ()#:transparent)
(struct boolT ()#:transparent)
(struct strT ()#:transparent)
(struct funT ([args : (Listof Ty)] [ret : Ty])#:transparent)

(struct bindingV ([name : Symbol] [val : (Boxof Value)])#:transparent)
(define-type Env (Listof bindingV))
(define top-env (list
                 (bindingV 'true (box (boolV #t)))
                 (bindingV 'false (box (boolV #f)))
                 (bindingV '+ (box (primopV (lambda ([vals : (Listof Value)])
                                              (numV (+ (numV-n (cast (first vals) numV))
                                                       (numV-n (cast (second vals) numV))))))))
                 (bindingV '- (box (primopV (lambda ([vals : (Listof Value)])
                                              (numV (- (numV-n (cast (first vals) numV))
                                                       (numV-n (cast (second vals) numV))))))))
                 (bindingV '* (box (primopV (lambda ([vals : (Listof Value)])
                                              (numV (* (numV-n (cast (first vals) numV))
                                                       (numV-n (cast (second vals) numV))))))))
                 (bindingV '/ (box (primopV (lambda ([vals : (Listof Value)])
                                              (let ([num1 (numV-n (cast (first vals) numV))]
                                                    [num2 (numV-n (cast (second vals) numV))])
                                                (cond [(equal? num2 0) (error "DUNQ: div by zero")]
                                                      [else (numV (/ num1 num2))]))))))
                 (bindingV '<= (box (primopV (lambda ([vals : (Listof Value)])
                                               (boolV (<= (numV-n (cast (first vals) numV))
                                                          (numV-n (cast (second vals) numV))))))))
                 (bindingV 'num-eq? (box (primopV (lambda ([vals : (Listof Value)])
                                                    (boolV (equal? (numV-n (cast (first vals) numV))
                                                                   (numV-n (cast (second vals) numV))))))))
                 (bindingV 'str-eq? (box (primopV (lambda ([vals : (Listof Value)])
                                                    (boolV (equal? (stringV-s (cast (first vals) stringV))
                                                                   (stringV-s (cast (second vals) stringV))))))))
                 (bindingV 'substring (box (primopV (lambda ([vals : (Listof Value)]) (substring-op vals)))))
                 ))

(struct bindingT ([name : Symbol] [type : Ty])#:transparent)
(define-type TEnv (Listof bindingT))
(define base-tenv (list
                   (bindingT 'true (boolT))
                   (bindingT 'false (boolT))
                   (bindingT '+ (funT (list (numT) (numT)) (numT)))
                   (bindingT '- (funT (list (numT) (numT)) (numT)))
                   (bindingT '* (funT (list (numT) (numT)) (numT)))
                   (bindingT '/ (funT (list (numT) (numT)) (numT)))
                   (bindingT '<= (funT (list (numT) (numT)) (boolT)))
                   (bindingT 'num-eq? (funT (list (numT) (numT)) (boolT)))
                   (bindingT 'str-eq? (funT (list (strT) (strT)) (boolT)))
                   (bindingT 'substring (funT (list (strT) (numT) (numT)) (strT)))
                   ))

;performs interpretation of DUNQ language and serializes output
(define (top-interp [s : Sexp]) : String
  (let ([pout (parse s)])
    (begin (type-check pout base-tenv) (serialize (interp pout (make-top-env))))))

;interprets a given ExprC into a real value, swapping in functions as needed.
(: interp (ExprC Env -> Value))
(define (interp expr env)
  (match expr
    [(numC val) (numV val)]
    [(idC id) (unbox (lookup id env))]
    [(setC var val)
     (let ([where (lookup var env)] [true-val (interp val env)])
       (begin (set-box! where true-val) (boolV #t)))]
    [(stringC s) (stringV s)]
    [(appC f as) (define f-value (interp f env))
                 (cond
                   [(and (closV? f-value) (equal? (length (closV-args f-value)) (length as)))
                    (interp (closV-body f-value)
                            (append
                             (map (lambda ([one-param : Symbol] [one-arg : ExprC])
                                    (bindingV one-param
                                             (box (interp one-arg env))))
                                  (closV-args f-value) as)
                             (closV-env f-value)))]
                   [else ((primopV-op (cast f-value primopV))
                          (map (lambda ([one-arg : ExprC]) (interp one-arg env)) as))])]
    [(lamC args _ body) (closV args body env)]
    [(ifC if then else) (cond
                          [(equal? (interp if env) (boolV #t)) (interp then env)]
                          [else (interp else env)])]
    [(recC rname rbody _ mbody) (define bind (bindingV rname ((inst box Value) (numV 1))))
                                (begin (set-box! (bindingV-val bind) (interp rbody (cons bind env)))
                                       (interp mbody (cons bind env)))]))

;interp helper, performs lookup of idC values on application
(: lookup (Symbol Env -> (Boxof Value)))
(define (lookup for env)
  (cond
    [(symbol=? for (bindingV-name (first env)))
     (bindingV-val (first env))]
    [else (lookup for (rest env))]))

;checks types before interpretation
(: type-check (ExprC TEnv -> Ty))
(define (type-check e env)
  (match e
    [(numC _) (numT)]
    [(stringC _) (strT)]
    [(idC id) (type-lookup id env)]
    [(setC var val)
     (let ([vartype (type-lookup var env)]
           [valtype (type-check val env)])
       (cond [(equal? vartype valtype) (boolT)]
             [else (error "DUNQ: type-check bad <- type")]))]
    [(ifC if then else)
     (define ift (type-check then env))
     (cond
       [(and (boolT? (type-check if env))
             (equal? ift (type-check else env))) ift]
       [else (error "DUNQ: type check bad if input")])]
    [(appC fun args)
     (let ([ft (type-check fun env)]
           [at (map (lambda ([onearg : ExprC]) (type-check onearg env)) args)])
       (cond
         [(and (funT? ft) (equal? (funT-args ft) at))
          (funT-ret ft)]
         [else (error "DUNQ: type check bad appC input")]))]
    [(lamC args argtypes body) (funT argtypes (type-check body (append (map bindingT args argtypes) env)))]
    [(recC name fun funtype mbody)
     (let* ([newenv (cons (bindingT name funtype) (append (map bindingT (lamC-args fun) (lamC-argsT fun)) env))])
       (cond
         [(equal? (type-check fun newenv) funtype) (type-check mbody newenv)]
         [else (error "DUNQ: type check bad recC input")]))]))

;type-check helper. looks up a given symbol type in type env
(: type-lookup (Symbol TEnv -> Ty))
(define (type-lookup sym env)
  (cond
    [(empty? env) (error "DUNQ: type not found")]
    [else (cond
            [(symbol=? sym (bindingT-name (first env)))
             (bindingT-type (first env))]
            [else (type-lookup sym (rest env))])]))

;parses a DUNQ function into an ExprC.
(: parse (Sexp -> ExprC))
(define (parse s)
  (match s
    [(? real? val) (numC val)]
    [(and id (? symbol?) (not ': '-> '<- 'vars 'rec 'if 'lam)) (idC id)]
    [(? string? s) (stringC s)]
    [(list (? symbol? var) '<- val) (setC var (parse val))]
    [(list 'if x then else) (ifC (parse x) (parse then) (parse else))]
    [(list 'lam (list (list (? symbol? args) ': argtypes) ...) body)
     #:when (or (empty? args) (arg-check (cast args (Listof Symbol))))
     (lamC (cast args (Listof Symbol)) (map parse-type (cast argtypes (Listof Sexp))) (parse body))]
    [(list 'vars (list (list (? symbol? allsym) ': alltypes alls) ...) expression)
     #:when (or (empty? allsym) (arg-check (cast allsym (Listof Symbol))))
     (appC
      (lamC
       (cast allsym (Listof Symbol))
       (map parse-type (cast alltypes (Listof Sexp)))
       (parse expression))
      (map (lambda ([x : Sexp]) (parse x)) (cast alls (Listof Sexp))))]
    [(list 'rec (list (list (? symbol? rname)
                            (list (? symbol? rargs) ': rargstypes) ...) ': (? symbol? rbodytype) rbody) mbody)
     (recC rname
           (cast (parse
                  `{lam ,(map (lambda ([onerarg : Symbol]
                                       [onerargtype : Sexp])
                                `[,onerarg : ,onerargtype])
                              (cast rargs (Listof Symbol))
                              (cast rargstypes (Listof Sexp))) ,rbody}) lamC)
           (parse-type `{,@(cast rargstypes (Listof Sexp)) -> ,rbodytype})
           (parse mbody))]
    [(list fun args ...) (appC (parse fun) (map parse args))]
    [else (error "DUNQ: bad input parse" s)]))

;parse helper. checks for repeted arg names.
(: arg-check ((Listof Symbol) -> Boolean))
(define (arg-check s)
  (cond
    [(empty? (rest s)) #t]
    [(member (first s) (rest s)) #f]
    [else (arg-check (rest s))]))

;parses DUNQ into types for verification later
(: parse-type (Sexp -> Ty))
(define (parse-type s)
  (match s
    ['num (numT)]
    ['bool (boolT)]
    ['str (strT)]
    [(list argtypes ... '-> restype)
     (funT (map parse-type (cast argtypes (Listof Sexp))) (parse-type restype))]
    [else (error "DUNQ: bad input parse-type")]))

;creates new top level for mutation
(define (make-top-env) : Env
  (cast top-env Env))

;serializes value into string
(: serialize (Value -> String))
(define (serialize val)
  (match val
    [(numV n) (~v n)]
    [(boolV #t) "true"]
    [(boolV #f) "false"]
    [(closV args body env) "#<procedure>"]
    [(? primopV?) "#<primop>"]
    [(stringV s) (~v s)]))

;performs substring operation on stringV and returns sub-StringV
(: substring-op ((Listof Value) -> Value))
(define (substring-op vals)
  (match vals
    [(list (stringV s) (numV start) (numV end))
     #:when (and (> (string-length s) start) (>= (string-length s) end) (integer? start) (integer? end))
     (stringV (substring s (cast start Integer) (cast end Integer)))]
    [else (error "DUNQ: bad substring")]))

(check-equal? (type-check (numC 1) base-tenv) (numT))
(check-equal? (type-check (idC 'true) base-tenv) (boolT))
(check-equal? (type-check (appC (idC '+) (list (numC 1) (numC 2))) base-tenv) (numT))
(check-equal? (parse-type '{num str -> bool}) (funT (list (numT) (strT)) (boolT)))
(check-equal? (arg-check `(hello hi how are you)) #t)
(check-equal? (arg-check `(hello hi how hi are)) #f)
(check-equal? (arg-check `(hello)) #t)
(check-equal? (parse '{if x x false}) (ifC (idC 'x) (idC 'x) (idC 'false)))
(check-exn (regexp (regexp-quote "DUNQ: bad input")) (lambda () (parse '{{{}} some bad input})))
(check-exn (regexp (regexp-quote "DUNQ: bad input")) (lambda () (parse '{+ vars if})))
(check-equal? (top-interp
               '{rec {{fact {n : num} {f : {num -> num}}} : num {if {num-eq? n 0} 1 {* n {f {fact {- n 1} f}}}}}
               {fact 2 {lam {{x : num}} {- x 10}}}}) "-38")
(check-equal? (top-interp '{lam {[x : num] [y : num]} {+ x y}}) "#<procedure>")
(check-exn (regexp (regexp-quote "DUNQ: type check bad appC input"))
           (lambda () (top-interp '{lam {[x : num] [y : bool]} {+ x y}})))
(check-equal? (top-interp '{{lam {[x : num] [y : num]} {+ x y}} 1 2}) "3")
(check-exn (regexp (regexp-quote "DUNQ: type check bad appC input"))
           (lambda () (top-interp '{{lam {[x : num] [y : num]} {+ x y}} 1 true})))
(check-equal? (top-interp '{lam {[x : num] [y : {num -> num}]} {y x}}) "#<procedure>")
(check-equal? (top-interp '{vars {{x : num 3} {y : {num num -> num} +}} {y x 1}}) "4")
(check-equal? (top-interp '{if true true false}) "true")
(check-equal? (top-interp '{if false true false}) "false")
(check-exn (regexp (regexp-quote "DUNQ: type check bad if input"))
           (lambda () (top-interp '{if "hi" 1 2})))
(check-exn (regexp (regexp-quote "DUNQ: bad input parse-type"))
           (lambda () (top-interp '{lam {[x : blah]} x})))
(check-equal? (top-interp '+) "#<primop>")
(check-equal? (top-interp '{/ 1 2}) "1/2")
(check-exn (regexp (regexp-quote "DUNQ: div by zero"))
           (lambda () (top-interp '{/ 1 0})))
(check-equal? (top-interp '{str-eq? "hello" "hello"}) "true")
(check-equal? (top-interp '{str-eq? "hello" "hi"}) "false")
(check-equal? (top-interp '{substring "hello" 1 3}) "\"el\"")
(check-exn (regexp (regexp-quote "DUNQ: bad substring"))
           (lambda () (top-interp '{substring "hello" 10 1})))
(check-equal? (top-interp '{<= 1 3}) "true")
(check-exn (regexp (regexp-quote "DUNQ: type not found"))
           (lambda () (top-interp '{lam {} {+ x 1}})))
(check-equal? (type-check (parse '{{lam {[x : num]} {x <- 1234}} 1}) base-tenv) (boolT))
(check-equal? (top-interp '{{lam {[x : num]} {x <- 1}} 3}) "true")
(check-exn (regexp (regexp-quote "DUNQ: type-check bad <- type"))
           (lambda () (top-interp '{lam {[x : num]} {x <- "hi"}})))
(check-exn (regexp (regexp-quote "DUNQ: type check bad recC input"))
           (lambda () (top-interp '{rec {{a {c : num}} : num "abc"} 13})))
