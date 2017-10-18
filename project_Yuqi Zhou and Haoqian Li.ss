;;edited by Yuqi Zhou and Haoqian Li of section 2
;:  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

(load "chez-init.ss") 

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

; parsed expression

(define-datatype expression expression?
  [var-exp
    (id symbol?)]
  [lit-exp
    (id lit?)]
  [lambda-exp-sym
    (id var-exp?)
    (exps (list-of expression?))]
  [lambda-exp-normal
    (ids (list-of var-exp?))
    (exps (list-of expression?))]
  [lambda-exp-improper
    (ids-before-dot (list-of var-exp?))
    (id-after-dot var-exp?)
    (exps (list-of expression?))]
  [if-exp-else
    (judge expression?)
    (truecase expression?)
    (falsecase expression?)]
  [if-exp-noelse
    (judge expression?)
    (truecase expression?)]
  [set!-exp
    (id var-exp?)
    (exp expression?)]
  [let-exp
    (variables (list-of var-exp?))
    (values (list-of expression?))
    (exps (list-of expression?))]
  [let*-exp
    (variables (list-of var-exp?))
    (values (list-of expression?))
    (exps (list-of expression?))]
  [letrec-exp
    (variables (list-of var-exp?))
    (values (list-of expression?))
    (exps (list-of expression?))]
  [namedlet-exp   
    (id var-exp?)
    (variables (list-of var-exp?))
    (values (list-of expression?))
    (exps (list-of expression?))]
  [app-exp
    (rator expression?)
    (rands (list-of expression?))]
  [cond-exp
    (exps (list-of expression?))
    (else-part expression?)]
  [begin-exp
    (exps (list-of expression?))]
  [or-exp
    (exps (list-of expression?))]
  [and-exp
    (exps (list-of expression?))]
  [case-exp
    (id expression?)
    (cases (list-of expression?))
    (exps (list-of expression?))
    (else-part expression?)]
  [while-exp
    (judge expression?)
    (exps (list-of expression?))])

	
	(define (lit? datum) 
  (ormap 
       (lambda (pred) (pred datum))
       (list number? vector? boolean? symbol? string? pair? null?)))

(define var-exp?
  (lambda (datum)
    (cases expression datum
      [var-exp (id) #t]
      [else #f])))

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?)))

; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [cr-proc
    (name symbol?)]
  [lambda-normal-proc
    (ids (list-of symbol?))
    (exps (list-of expression?))
    (env environment?)]
  [lambda-symbol-proc
    (id symbol?)
    (exps (list-of expression?))
    (env environment?)]
  [lambda-improper-proc
    (ids (list-of symbol?))
    (exps (list-of expression?))
    (env environment?)])
	 
	

;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+


; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

(define (get-first-part lst)
  (if (symbol? (cdr lst)) (list (car lst)) (cons (car lst) (get-first-part (cdr lst)))))

(define (get-last-ele lst)
  (if (symbol? (cdr lst)) (cdr lst) (get-last-ele (cdr lst))))

(define parse-exp         
  (lambda (datum)
    (cond
      [(symbol? datum) (var-exp datum)]
      [(pair? datum)
        (cond
          [(not (list? datum)) (eopl:error 'parse-exp "expression ~s is not a proper list" datum)]
          [(eqv? (car datum) 'lambda)
            (cond
              [(< (length datum) 3) (eopl:error 'parse-exp "lambda-expression: incorrect length ~s" datum)]
              [(symbol? (2nd datum)) 
                (lambda-exp-sym (var-exp (2nd datum))
                (map parse-exp (cddr datum)))]
              [(list? (2nd datum))
                (if (andmap symbol? (2nd datum))
                  (lambda-exp-normal
                    (map var-exp (2nd datum))
                    (map parse-exp (cddr datum))) 
                  (eopl:error 'parse-exp "lambda's formal arguments ~s must all be symbols" (2nd datum)))]
              [else 
                (lambda-exp-improper
                  (map var-exp (get-first-part (2nd datum)))
                  (var-exp (get-last-ele (2nd datum)))
                  (map parse-exp (cddr datum)))])]
          [(eqv? (car datum) 'if)
            (if (< (length datum) 3)
              (eopl:error 'parse-exp "if-expression ~s does not have (only) test, then, and else" datum)
              (if (null? (cdddr datum))
                (if-exp-noelse (parse-exp (2nd datum))
                  (parse-exp (3rd datum)))
              (if-exp-else (parse-exp (2nd datum))
                (parse-exp (3rd datum))
                (parse-exp (4th datum)))))]
          [(eqv? (car datum) 'set!)
            (if (= (length datum) 3)
              (set!-exp (var-exp (2nd datum))
              (parse-exp (3rd datum))) 
              (eopl:error 'parse-exp "set! expression ~s does not have (only) variable and expression" datum))]
          [(eqv? (car datum) 'let)
            (cond
              [(< (length datum) 3)
                (eopl:error 'parse-exp "~s-expression has incorrect length ~s" datum)]
              [(symbol? (2nd datum))
                (cond
                  [(not (list? (3rd datum)))
                    (eopl:error 'parse-exp "declarations in ~s-expression not a list ~s" datum)]
                  [(not (andmap list? (3rd datum)))
                    (eopl:error 'parse-exp "declaration in ~s-exp is not a proper list ~s" datum)]
                  [(not (andmap (lambda (x) (if (= (length x) 2) #t #f)) (3rd datum)))
                    (eopl:error 'parse-exp "declaration in ~s-exp must be a list of length 2 ~s" datum)]
                  [(not (andmap (lambda (x) (symbol? (car x))) (3rd datum)))
                    (eopl:error 'parse-exp "vars in ~s-exp must be symbols ~s" datum)]
                  [else (namedlet-exp (var-exp (2nd datum))
                    (map var-exp (map car (3rd datum)))
                    (map parse-exp (map cadr (3rd datum)))
                    (map parse-exp (cdddr datum)))])]
              [else 
                (cond
                  [(not (list? (2nd datum)))
                    (eopl:error 'parse-exp "declarations in ~s-expression not a list ~s" datum)]
                  [(not (andmap list? (2nd datum)))
                    (eopl:error 'parse-exp "declaration in ~s-exp is not a proper list ~s" datum)]
                  [(not (andmap (lambda (x) (if (= (length x) 2) #t #f)) (2nd datum)))
                    (eopl:error 'parse-exp "declaration in ~s-exp must be a list of length 2 ~s" datum)]
                  [(not (andmap (lambda (x) (symbol? (car x))) (2nd datum)))
                    (eopl:error 'parse-exp "vars in ~s-exp must be symbols ~s" datum)]
                  [else (let-exp (map var-exp (map car (2nd datum)))
                    (map parse-exp (map cadr (2nd datum)))
                    (map parse-exp (cddr datum)))])])]
          [(eqv? (car datum) 'let*)
            (cond
              [(< (length datum) 3)
                (eopl:error 'parse-exp "~s-expression has incorrect length ~s" datum)]
              [(not (list? (2nd datum)))
                (eopl:error 'parse-exp "declarations in ~s-expression not a list ~s" datum)]
              [(not (andmap list? (2nd datum)))
                (eopl:error 'parse-exp "declaration in ~s-exp is not a proper list ~s" datum)]
              [(not (andmap (lambda (x) (if (= (length x) 2) #t #f)) (2nd datum)))
                (eopl:error 'parse-exp "declaration in ~s-exp must be a list of length 2 ~s" datum)]
              [(not (andmap (lambda (x) (symbol? (car x))) (2nd datum)))
                (eopl:error 'parse-exp "vars in ~s-exp must be symbols ~s" datum)]
              [else (let*-exp (map var-exp (map car (2nd datum)))
                (map parse-exp (map cadr (2nd datum)))
                (map parse-exp (cddr datum)))])]
          [(eqv? (car datum) 'letrec)
            (cond
              [(< (length datum) 3)
                (eopl:error 'parse-exp "~s-expression has incorrect length ~s" datum)]
              [(not (list? (2nd datum)))
                (eopl:error 'parse-exp "declarations in ~s-expression not a list ~s" datum)]
              [(not (andmap list? (2nd datum)))
                (eopl:error 'parse-exp "declaration in ~s-exp is not a proper list ~s" datum)]
              [(not (andmap (lambda (x) (if (= (length x) 2) #t #f)) (2nd datum)))
                (eopl:error 'parse-exp "declaration in ~s-exp must be a list of length 2 ~s" datum)]
              [(not (andmap (lambda (x) (symbol? (car x))) (2nd datum)))
                (eopl:error 'parse-exp "vars in ~s-exp must be symbols ~s" datum)]
              [else (letrec-exp (map var-exp (map car (2nd datum)))
                (map parse-exp (map cadr (2nd datum)))
                (map parse-exp (cddr datum)))])]
          [(and (list? (car datum)) (= (length datum) 1) (eqv? (caar datum) 'lambda))
            (lit-exp datum)]
          [(eqv? (car datum) 'cond)
            (let ([else-part (find-else (cdr datum))])
              (if (eqv? (caar else-part) 'else)
                (cond-exp (map parse-exp (find-firsts (cdr datum))) (parse-exp (cadar else-part)))
                (cond-exp (map parse-exp (cdr datum)) (parse-exp 'void))))]
          [(eqv? (car datum) 'begin)
            (begin-exp (map parse-exp (cdr datum)))]
          [(eqv? (car datum) 'or)
            (or-exp (map parse-exp (cdr datum)))]
          [(eqv? (car datum) 'and)
            (and-exp (map parse-exp (cdr datum)))]
          [(eqv? (car datum) 'case)
            (case-exp (parse-exp (cadr datum))
              (map (lambda (x) (lit-exp (car x))) (find-firsts (cddr datum)))
              (map (lambda (x) (parse-exp (cadr x))) (find-firsts (cddr datum)))
              (parse-exp (cadar (find-else (cddr datum)))))]
          [(eqv? (car datum) 'while)
            (while-exp (parse-exp (cadr datum)) (map parse-exp (cddr datum)))]
          [(or (eqv? (car datum) 'quote) (not (lit? (car datum))))
            (if (eqv? (car datum) 'quote) 
              (lit-exp (cadr datum))
             (lit-exp datum))]
          [else (app-exp (parse-exp (car datum)) (map parse-exp (cdr datum)))])]
      [(lit? datum) (lit-exp datum)]
      [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))


(define (find-firsts datum)
  (if (null? (cdr datum)) '() (cons (car datum) (find-firsts (cdr datum)))))

(define (find-else datum)
  (if (null? (cdr datum)) datum (find-else (cdr datum))))



;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+





; Environment definitions for CSSE 304 Scheme interpreter.  
; Based on EoPL sections 2.2 and 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
     ((null? ls) #f)
     ((pred (car ls)) 0)
     (else (let ((list-index-r (list-index pred (cdr ls))))
	     (if (number? list-index-r)
		 (+ 1 list-index-r)
		 #f))))))

(define apply-env
  (lambda (env sym succeed fail) ; succeed and fail are "callback procedures, 
    (cases environment env       ;  succeed is appluied if sym is found, otherwise 
      [empty-env-record ()       ;  fail is applied.
        fail]
      [extended-env-record (syms vals env)
		(let ((pos (list-find-position sym syms)))
      	  (if 	(number? pos)
				(succeed (list-ref vals pos))
				(apply-env env sym succeed fail)))])))








;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+



; To be added later









;-------------------+
;                   |
;   INTERPRETER    |
;                   |
;-------------------+



; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form (empty-env))))

(define (syntax-expand exp)
  (cases expression exp
    [lambda-exp-normal (ids exps)
      (lambda-exp-normal ids (map syntax-expand exps))]
    [lambda-exp-sym (id exps)
      (lambda-exp-sym id (map syntax-expand exps))]
    [lambda-exp-improper (ids-before-dot id-after-dot exps)
      (lambda-exp-improper ids-before-dot id-after-dot (map syntax-expand exps))]
    [if-exp-else (judge truecase falsecase)
      (if-exp-else (syntax-expand judge) (syntax-expand truecase) (syntax-expand falsecase))]
    [if-exp-noelse (judge truecase)
      (if-exp-noelse (syntax-expand judge) (syntax-expand truecase))]
    [set!-exp (id exp)
      (set!-exp id (syntax-expand exp))]
    [let-exp (variables values exps)
      (app-exp (lambda-exp-normal variables (map syntax-expand exps)) (map syntax-expand values))]
    [let*-exp (variables values exps)
      (if (null? (cdr variables)) 
        (app-exp (lambda-exp-normal (list (car variables))
          (map syntax-expand exps))
        (list (syntax-expand (car values))))
        (app-exp (lambda-exp-normal (list (car variables))
          (list (syntax-expand (let*-exp (cdr variables) (cdr values) exps))))
        (list (syntax-expand (car values)))))]
    [letrec-exp (variables values exps)
      (letrec-exp (map syntax-expand variables) (map syntax-expand values) (map syntax-expand exps))]
    [namedlet-exp (id variables values exps)
      (namedlet-exp id (map syntax-expand variables) (map syntax-expand values) (map syntax-expand exps))]
    [app-exp (rator rands)
      (app-exp (syntax-expand rator) (map syntax-expand rands))]
    [cond-exp (exps else-part)
      (if (null? exps)
        else-part
        (if (and (equal? else-part (parse-exp 'void)) (null? (cdr exps)))
          (if-exp-noelse
            (syntax-expand (cadar exps))
            (syntax-expand (car (caddar exps))))
          (if-exp-else (syntax-expand (cadar exps))
            (syntax-expand (car (caddar exps)))
            (syntax-expand (cond-exp (cdr exps) else-part)))))]
    [begin-exp (exps)
      (lambda-exp-normal '() (map syntax-expand exps))]
    [or-exp (exps)
      (if (null? exps)
        (parse-exp #f)
        (app-exp (lambda-exp-normal (list (parse-exp 'carexp)) 
         (list (if-exp-else (parse-exp 'carexp) (parse-exp 'carexp) (syntax-expand (or-exp (cdr exps)))))) (list (syntax-expand (car exps)))))]
    [and-exp (exps)
      (cond
        [(null? exps) (parse-exp #t)]
        [(null? (cdr exps)) (car exps)]
        [else (if-exp-else (syntax-expand (car exps)) (syntax-expand (and-exp (cdr exps))) (parse-exp #f))])]
    [case-exp (id cases exps else-part)
      (if (null? cases) else-part
        (if-exp-else (app-exp (var-exp 'member) (list (syntax-expand id) (syntax-expand (car cases))))
          (syntax-expand (car exps))
          (syntax-expand (case-exp id (cdr cases) (cdr exps) else-part))))]
    [else exp]))

; eval-exp is the main component of the interpreter
(define eval-exp
  (lambda (exp env)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
        (if (crfam? (string->list (symbol->string id)) 'c) (cr-proc id)
				(apply-env env id; look up its value.
      	   (lambda (x) x) ; procedure to call if it is in the environment 
              (apply-env global-env
                id
                (lambda (x) x)
                (lambda () (eopl:error 'apply-env ; procedure to call if it is not in env
		          "variable not found in environment: ~s"
			   id)))))]
      [if-exp-else (judge truecase falsecase)
          (if (eval-exp judge env) (eval-exp truecase env) (eval-exp falsecase env))]
      [if-exp-noelse (judge truecase)
          (if (eval-exp judge env) (eval-exp truecase env))]
      [let-exp (variables values exps)
       (let ([new-env (extend-env (map var->sym variables)
                                  (eval-rands values env) env)]) (execute exps new-env))]
      [lambda-exp-normal (ids exps)
        (if (null? ids) (execute exps env)
        (lambda-normal-proc (map var->sym ids) exps env))]
      [lambda-exp-sym (id exps)
        (lambda-symbol-proc (var->sym id) exps env)]
      [lambda-exp-improper (ids-before-dot id-after-dot exps)
        (lambda-improper-proc (map var->sym (append ids-before-dot (list id-after-dot))) exps env)]
      [app-exp (rator rands)
        (let ([proc-value (eval-exp rator env)]
              [args (eval-rands rands env)])
          (apply-proc proc-value args))]
      [while-exp (judge exps)
        (if (eval-exp judge env) (begin (execute exps env) (eval-exp (while-exp judge exps) env)))]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

(define (var->sym var)
  (cases expression var
    [var-exp (id) id]
    [else #t]))

(define (execute exps env)
  (if (null? (cdr exps)) (eval-exp (car exps) env)
      (begin (eval-exp (car exps) env) (execute (cdr exps) env))))

(define (crfam? id match)
  (cond
    [(null? id) #f]
    [(eqv? match 'c) (crfam? (cdr id) 'n)]
    [(null? (cdr id)) (eqv? (car id) #\r)]
    [(or (eqv? (car id) #\d) (eqv? (car id) #\a)) (crfam? (cdr id) 'n)]
    [else #f]))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env)
    (map (lambda (e) (eval-exp e env)) rands))) 

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      [cr-proc (op) (apply-cr-proc (string->list (symbol->string op)) (car args))]
      [lambda-normal-proc (ids exps env)
        (if (null? ids) (execute exps env)
        (let ([new-env (extend-env ids args env)])
          (execute exps new-env)))]
      [lambda-symbol-proc (id exps env)
        (let ([new-env (extend-env (list id) (list args) env)])
          (execute exps new-env))]
      [lambda-improper-proc (ids exps env)
        (let ([new-env (extend-env ids (make-args-improper ids args) env)])
          (execute exps new-env))]
			; You will add other cases
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))

(define (make-args-improper ids args)
  (if (null? (cdr ids)) (list args) (cons (car args) (make-args-improper (cdr ids) (cdr args)))))

(define *prim-proc-names* '(+ - * / add1 sub1 cons = not zero? 
                            >= > < list null? eq? equal? length assq
                            atom? list->vector list? pair? procedure?
                            vector->list vector make-vector vector-ref
                            vector? number? symbol? set-car! set-cdr!
                            vector-set! display newline map apply member 
                            quotient))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))
(define global-env init-env)
; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (/ (1st args) (2nd args))]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(=) (= (1st args) (2nd args))]
      [(not) (apply not args)]
      [(zero?) (apply zero? args)]
      [(>=) (>= (1st args) (2nd args))]
      [(>) (> (1st args) (2nd args))]
      [(<) (< (1st args) (2nd args))]
      [(list) (apply list args)]
      [(null?) (null? (1st args))]
      [(eq?) (eq? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(length) (apply length args)]
      [(assq) (assq (1st args) (cdr args))]
      [(atom?) (atom? (1st args))]
      [(list->vector) (list->vector (1st args))]
      [(list?) (list? (1st args))]
      [(pair?) (pair? (1st args))]
      [(procedure?) (proc-val? (1st args))]
      [(vector->list) (vector->list (1st args))]
      [(vector) (apply vector args)]
      [(make-vector) (make-vector (1st args))]
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(vector?) (vector? (1st args))]
      [(number?) (number? (1st args))]
      [(symbol?) (symbol? (1st args))]
      [(set-car!) (set-car! (1st args) (2nd args))]
      [(set-cdr!) (set-cdr! (1st args) (2nd args))]
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(display) (display (1st args))]
      [(newline) (newline)]
      [(map) (map (lambda (x) (apply-proc (1st args) (list x))) (2nd args))]
      [(apply) (apply-proc (1st args) (2nd args))]
      [(member) (member (1st args) (2nd args))]
      [(quotient) (quotient (1st args) (2nd args))]
      [else (error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-proc)])))

(define apply-cr-proc
  (lambda (op args)
    (cond
      [(eqv? #\c (car op)) (apply-cr-proc (cdr op) args)]
      [(eqv? #\d (car op)) (cdr (apply-cr-proc (cdr op) args))]
      [(eqv? #\a (car op)) (car (apply-cr-proc (cdr op) args))]
      [else args])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x)
    (top-level-eval (syntax-expand (parse-exp x)))))