;; ** The TOY interpreter

#lang pl 12

;;; ----------------------------------------------------------------
;;; Syntax

#| The BNF:
   <TOY> ::= <num>
           | <id>
           | { bind {{ <id> <TOY> } ... } <TOY> <TOY> ... }
           | { bindrec {{ <id> <TOY> } ... } <TOY> <TOY> ... }
           | { fun { <id> ... } <TOY> <TOY> ... }
           | { if <TOY> <TOY> <TOY> }
           | { <TOY> <TOY> ... }
           | { set! <id> <TOY> }
|#

;; A matching abstract syntax tree datatype:
(define-type TOY
  [Num  Number]
  [Id   Symbol]
  [Bind (Listof Symbol) (Listof TOY) (Listof TOY)]
  [BindRec (Listof Symbol) (Listof TOY) (Listof TOY)]
  [Fun  (Listof Symbol) (Listof TOY)]
  [Call TOY (Listof TOY)]
  [If   TOY TOY TOY]
  [Set  Symbol TOY])

(: unique-list? : (Listof Any) -> Boolean)
;; Tests whether a list is unique, guards Bind and Fun values.
(define (unique-list? xs)
  (or (null? xs)
      (and (not (member (first xs) (rest xs)))
           (unique-list? (rest xs)))))

(: parse-sexpr : Sexpr -> TOY)
;; parses s-expressions into TOYs
(define (parse-sexpr sexpr)
  (match sexpr
    [(number: n)    (Num n)]
    [(symbol: name) (Id name)]
    [(cons (and binder (or 'bind 'bindrec)) more)
     (match sexpr
       [(list _ (list (list (symbol: names) (sexpr: nameds)) ...)
              body0 body ...)
        (if (unique-list? names)
            ((if (eq? binder 'bind) Bind BindRec)
             names (map parse-sexpr nameds)
             (map parse-sexpr (cons body0 body)))
            (error 'parse-sexpr "duplicate `~s' names: ~s"
                   binder names))]
       [else (error 'parse-sexpr "bad `~s' syntax in ~s"
                    binder sexpr)])]
    [(cons 'fun more)
     (match sexpr
       [(list 'fun (list (symbol: names) ...)
              body0 body ...)
        (if (unique-list? names)
            (Fun names (map parse-sexpr (cons body0 body)))
            (error 'parse-sexpr "duplicate `fun' names: ~s" names))]
       [else (error 'parse-sexpr "bad `fun' syntax in ~s" sexpr)])]
    [(cons 'if more)
     (match sexpr
       [(list 'if cond then else)
        (If (parse-sexpr cond)
            (parse-sexpr then)
            (parse-sexpr else))]
       [else (error 'parse-sexpr "bad `if' syntax in ~s" sexpr)])]
        [(cons 'set! more)
     (match sexpr 
       [(list 'set! (symbol: id) expr)
        (Set id (parse-sexpr expr))]
       [else (error 'parse-sexpr "bad `set' syntax in ~s" sexpr)])]
    [(list fun args ...) ; other lists are applications
     (Call (parse-sexpr fun)
           (map parse-sexpr args))]
    [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))

(: parse : String -> TOY)
;; Parses a string containing an TOY expression to a TOY AST.
(define (parse str)
  (parse-sexpr (string->sexpr str)))

;;; ----------------------------------------------------------------
;;; Values and environments

(define-type ENV
  [EmptyEnv]
  [FrameEnv FRAME ENV])

;; a frame is an association list of names and values.
(define-type FRAME = (Listof (List Symbol (Boxof VAL))))

(define-type VAL
  [RktV  Any]
  [FunV  (Listof Symbol) (Listof TOY) ENV]
  [PrimV ((Listof VAL) -> VAL)]
  [BogusV])

(define the-bogus-value (BogusV))

(: extend : (Listof Symbol) (Listof VAL) ENV -> ENV)
;; extends an environment with a new frame.
(define (extend names values env)
  (raw-extend names (map (inst box VAL) values) env))

(: raw-extend : (Listof Symbol) (Listof (Boxof VAL)) ENV -> ENV)
;; extends an environment with a new frame, using boxed values.
(define (raw-extend names boxed-values env)
  (if (= (length names) (length boxed-values))
      (FrameEnv (map (λ ([name : Symbol] [val : (Boxof VAL)])
                       (list name val))
                     names boxed-values)
                env)
      (error 'raw-extend "arity mismatch for names: ~s" names)))

(: extend-rec : (Listof Symbol) (Listof TOY) ENV -> ENV)
;; extends an environment with a new recursive frame.
(define (extend-rec names exprs env)
  (let* ([bogus-values (map (λ ([name : Symbol]) the-bogus-value) names)]
         [new-env (extend names bogus-values env)]
         [values (map (λ ([expr : TOY]) (eval expr new-env)) exprs)])
    (for-each (λ ([name : Symbol] [value : VAL])
                (let ([cell (lookup name new-env)])
                  (set-box! cell value)))
              names values) 
    new-env))

(: lookup : Symbol ENV -> (Boxof VAL))
;; lookup a symbol in an environment, frame by frame,
;; return its value or throw an error if it isn't bound
(define (lookup name env)
  (cases env
    [(EmptyEnv) (error 'lookup "no binding for ~s" name)]
    [(FrameEnv frame rest)
     (let ([cell (assq name frame)])
       (if cell
           (second cell)
           (lookup name rest)))]))

(: unwrap-rktv : VAL -> Any)
;; helper for `racket-func->prim-val': unwrap a RktV wrapper in
;; preparation to be sent to the primitive function
(define (unwrap-rktv x)
  (cases x
    [(RktV v) v]
    [else (error 'racket-func "bad input: ~s" x)]))

(: racket-func->prim-val : Function -> (Boxof VAL))
;; converts a racket function to a primitive evaluator function
;; which is a PrimV holding a ((Listof VAL) -> VAL) function.
;; (the resulting function will use the list function as is,
;; and it is the list function's responsibility to throw an error
;; if it's given a bad number of arguments or bad input types.)
(define (racket-func->prim-val racket-func)
  (define list-func (make-untyped-list-function racket-func))
  (box (PrimV (lambda (args)
                (RktV (list-func (map unwrap-rktv args)))))))

;; The global environment has a few primitives:
(: global-environment : ENV)
(define global-environment
  (FrameEnv (list (list '+ (racket-func->prim-val +))
                  (list '- (racket-func->prim-val -))
                  (list '* (racket-func->prim-val *))
                  (list '/ (racket-func->prim-val /))
                  (list '< (racket-func->prim-val <))
                  (list '> (racket-func->prim-val >))
                  (list '= (racket-func->prim-val =))
                  ;; values
                  (list 'true  (box (RktV #t)))
                  (list 'false (box (RktV #f))))
            (EmptyEnv)))

;;; ----------------------------------------------------------------
;;; Evaluation

(: eval-body : (Listof TOY) ENV -> VAL)
;; evaluates a list of expressions, returns the last value.
(define (eval-body exprs env)
  (match exprs
    [(list expr) (eval expr env)]
    [(cons expr more)
     (let ([x (eval expr env)]) (eval-body more env))]))

(: eval : TOY ENV -> VAL)
;; evaluates TOY expressions
(define (eval expr env)
  ;; convenient helper
  (: eval* : TOY -> VAL)
  (define (eval* expr) (eval expr env))
  (cases expr
    [(Num n)   (RktV n)]
    [(Id name) (unbox (lookup name env))]
    [(Bind names exprs bound-bodies)
     (eval-body bound-bodies (extend names (map eval* exprs) env))]
    [(BindRec names exprs bound-bodies)
     (eval-body bound-bodies (extend-rec names exprs env))]
    [(Fun names bound-bodies)
     (FunV names bound-bodies env)]
    [(Call fun-expr arg-exprs)
     (let ([fval (eval* fun-expr)]
           [arg-vals (map eval* arg-exprs)])
       (cases fval
         [(PrimV proc) (proc arg-vals)]
         [(FunV names bodies fun-env)
          (eval-body bodies (extend names arg-vals fun-env))]
         [else (error 'eval "function call with a non-function: ~s"
                      fval)]))]
    [(If cond-expr then-expr else-expr)
     (eval* (if (cases (eval* cond-expr)
                  [(RktV v) v] ; Racket value => use as boolean
                  [else #t])   ; other values are always true
                then-expr
                else-expr))]
    [(Set id expr)
     (let ([x (set-box! (lookup id env)
                        (eval expr env))])
       the-bogus-value)]))

(: run : String -> Any)
;; evaluate a TOY program contained in a string
(define (run str)
  (let ([result (eval (parse str) global-environment)])
    (cases result
      [(RktV v) v]
      [else (error 'run "evaluation returned a bad value: ~s"
                   result)])))

;;; ----------------------------------------------------------------
;;; Tests

(test (run "{{fun {x} {+ x 1}} 4}")
      => 5)
(test (run "{bind {{add3 {fun {x} {+ x 3}}}} {add3 1}}")
      => 4)
(test (run "{bind {{add3 {fun {x} {+ x 3}}}
                   {add1 {fun {x} {+ x 1}}}}
              {bind {{x 3}} {add1 {add3 x}}}}")
      => 7)
(test (run "{bind {{identity {fun {x} x}}
                   {foo {fun {x} {+ x 1}}}}
              {{identity foo} 123}}")
      => 124)
(test (run "{bind {{x 3}}
              {bind {{f {fun {y} {+ x y}}}}
                {bind {{x 5}}
                  {f 4}}}}")
      => 7)
(test (run "{{{fun {x} {x 1}}
              {fun {x} {fun {y} {+ x y}}}}
             123}")
      => 124)

;; Tests for set
(test (run "{set! x 1}")
      =error> "no binding for x")
(test (run "{set! x}")
      =error> "bad `set' syntax")
(test (run "{bind {{x 1}}
              {set! x 0}}")
     =error> "evaluation returned a bad value")
(test (run "{bind {{x 1}}
                      {bind {{y {set! x 4}}}
                         x}}") => 4)
(test (run "{bind {{f {fun {x}
                        {bind {{y {set! x {if {< x 3} 4 x}}}}
                          x}}}} {f 0}}") => 4)

;; Tests for bindrec
(test (run "{bindrec x}")
      =error> "bad `bindrec' syntax")
(test (run "{bindrec {{x 1}
                      {x 2}}
              x}")
      =error> "duplicate `bindrec' names")
(test (run "{bindrec {{fact {fun {n}
                              {if {= 0 n}
                                1
                                {* n {fact {- n 1}}}}}}}
              {fact 5}}")
      => 120)
;; contrived but simple mutually recursive case
(test (run "{bindrec {{double {fun {n}
                                     {if {> n 10}
                                         n
                                         {increment {* n 2}}}}}
                      {increment {fun {n}
                                     {if {> n 10}
                                         n
                                         {double {+ n 1}}}}}}
             {double 2}}")
      => 11)

;; Tests for multiple body expressions
;; check it errors when no bodies given
(test (run "{fun {x}}")
      =error> "bad `fun' syntax")
(test (run "{bind {{x 1}}}")
      =error> "bad `bind' syntax")
(test (run "{bindrec {{x 1}}}")
      =error> "bad `bindrec' syntax")
;; bind with multi-expressions
(test (run "{bind {{x 1}}
              {set! x 4}
              x}") => 4)
;; TODO: bindrec with multi-expressions
;; TODO: fun with multi-expressions
(test (run "{bind {{make-counter
                     {fun {}
                       {bind {{c 0}}
                         {fun {}
                           {set! c {+ 1 c}}
                           c}}}}}
              {bind {{c1 {make-counter}}
                     {c2 {make-counter}}}
                {* {c1} {c1} {c2} {c1}}}}")
      => 6)
(test (run "{bindrec {{foo {fun {}
                             {set! foo {fun {} 2}}
                             1}}}
              {+ {foo} {* 10 {foo}}}}")
      => 21)

;; Tests for by-reference function arguments
;; ...

;; More tests for complete coverage
(test (run "{bind x 5 x}")      =error> "bad `bind' syntax")
(test (run "{fun x x}")         =error> "bad `fun' syntax")
(test (run "{if x}")            =error> "bad `if' syntax")
(test (run "{}")                =error> "bad syntax")
(test (run "{bind {{x 5} {x 5}} x}") =error> "duplicate*bind*names")
(test (run "{fun {x x} x}")     =error> "duplicate*fun*names")
(test (run "{+ x 1}")           =error> "no binding for")
(test (run "{+ 1 {fun {x} x}}") =error> "bad input")
(test (run "{+ 1 {fun {x} x}}") =error> "bad input")
(test (run "{1 2}")             =error> "with a non-function")
(test (run "{{fun {x} x}}")     =error> "arity mismatch")
(test (run "{if {< 4 5} 6 7}")  => 6)
(test (run "{if {< 5 4} 6 7}")  => 7)
(test (run "{if + 6 7}")        => 6)
(test (run "{fun {x} x}")       =error> "returned a bad value")

;;; ----------------------------------------------------------------