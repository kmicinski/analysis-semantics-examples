#lang racket
;; v0.0 April 8, 2024 -- WORKING NOTES (could have bugs!) 

;; Apply/Eval Refactoring -- Semantics Homework
;;
;; Kris Micinski (kkmicins@syr.edu and krismicinski@gmail.com)
;;
;; Warning: may be buggy, please contact kris if you notice
;; obvious bugs.
(provide (all-defined-out))

;; The purpose of this handout / exercise / homework is to
;; teach you the eval/apply refactoring trick, which enables
;; handling more complex direct-style forms in the abstract
;; machine per-se, rather than assuming an A-normalization
;; pass.
;;
;; In more traditional languages (LLVM, etc...), compilation
;; occurs down to a more SSA-like IR, which is the procedural
;; variant of an A-normalized IR. In practice, you will probably
;; often be defining interpreters which evaluate A-normalized
;; languages. Think about, e.g., Java bytecode: arguments to
;; expressions are always atomic, meaning that the structure
;; of continuations is much simpler than you would otherwise
;; need in this setting.
;;
;; However, if you do want to do interpretation of a direct-style
;; langauge, you should strongly consider taking inspiration
;; from the approach here: evaluation and application (returns)
;; are handled independently, with rules mitigating their
;; interaction.

;;
;; Source language
;;


;; We will build an interpreter for this direct-style
;; language, which includes explicitly-tagged primitives,
;; λs, applications, literals, if, and letrec.
(define (expr? e)
  (match e
    [`(prim ,op ,es ...) #t]
    [`(λ (,xs ...) ,e) #t]
    [`(,es ,e-args ...) #t]
    [(? number? n) #t]
    [(? boolean? b) #t]
    [`(if ,e-g ,e-t ,e-f) #t]
    [`(letrec ([,f (λ (,x) ,e-b)]) ,e) #t]
    [_ #f]))

;;
;; We will use a CESK-style machine. But here, we have
;; two distinct kinds of machine states: E states
;; evaluate a value e in the context of an environment ρ,
;; but A states apply a value to a continuation.
;; 
;; More precise as to the exact structure, we will have:
;;  Eval states, evaluate an expression -- ⟨E e ρ σ κ⟩
;;  Apply states, apply a continuation -- ⟨A v σ κ⟩
;;
;; Formally, we say Σ is a disjoint union of these two
;; types of states. With respect to implementation that
;; means: we tag states and can recognize they are either
;; E/A very easily (matching).
;;
;; The purpose of the Eval/Apply refactoring is to
;; cleanly separate "evaluating into a term" and "returing
;; a value" (applying a continuation).
;;
;; Put simply: if we don't do a refactoring like this
;; (or assume a prior A-normalization pass), we will
;; get an explosion of continuations.
;; 

;;
;; Question: why do A states *not need* an environment?
;;

;; Here is the injection function into the machine's state space
(define (inj e)
  `(E ,e ,(hash) ,(hash) Done))

;; We will use an explicit continuation for now--store
;; allocating the continuation would be required for
;; AAM to work.
;;
;; I will write state rather than ς as it is simpler to
;; write in code :-) 

;; storable? values -- things the machine can store, and also things
;; that A states will carry
(define (storable? v)
  (match v
    [(? number? n) #t]
    [(? boolean? b) #t]
    [`(clo ,e ,env) #t]
    [_ #f]))

;; The step function takes states to states
(define (step state)
  (match state
    ;;
    ;; Eval states -- ⟨E e ρ σ κ⟩, must be total in e
    ;; 

    ;; Evaluate a variable--look it up and return it
    ;; to the proximate continuation
    [`(E ,(? symbol? x) ,env ,sto ,k)
     `(A ,(hash-ref sto (hash-ref env x)) ,sto ,k)]
    
    ;; Evaluate a λ, build a closure
    [`(E (λ (,xs ...) ,e) ,env ,sto ,k)
     `(A (clo (λ (,@xs) ,e) ,env) ,sto ,k)]
    ;; Lits eval to themselves
    [`(E ,(? boolean? b) ,env ,sto ,k)
     `(A ,b ,sto ,k)]
    [`(E ,(? number? n) ,env ,sto ,k)
     `(A ,n ,sto ,k)]
    ;; Ifs build a closure to suspend the decision
    [`(E (if ,e-g ,e-t ,e-f) ,env ,sto ,k)
     `(E ,e-g ,env ,sto (if-decide ,e-t ,e-f ,env ,k))]

    ;; Evaluating calls to prims / closures
    [`(E (prim ,op ,es ...) ,env ,sto ,k)
                             ;; vv eval-args-prim is a continuation which tracks
                             ;; - exprs left to go
                             ;; - values got so far
                             ;; - when exprs hits '() we're "done" and apply op
     `(E ,(first es) ,env ,sto (eval-args-prim ,op ,(rest es) () ,env ,k))]

    ;; Evaluating application of a closure--similar trick
    [`(E (,e-f ,es ...) ,env ,sto ,k)
     `(E ,e-f ,env ,sto (eval-args ,es () ,env ,k))]
    
    ;; Letrec: how do you do it?
    [`(E (letrec ([,f (λ (,x) ,e-b)]) ,e) ,env ,sto ,k) 'todo]
    
    ;;
    ;; Apply / Return states
    ;;

    ;; Primitives / builtins
    
    ;; Returning a storable value to a primitive when it's the last thing
    ;; Now you actually need to *do* the primitive to return its value
    [`(A ,(? storable? v) ,sto (eval-args-prim ,op () ,vs ,env+ ,k))
     (define v-r (apply (eval op (make-base-namespace)) (append vs (list v))))
     ;; now, we return v to k
     `(A ,v-r ,sto ,k)]
    ;; keep going with an op
    [`(A ,(? storable? v) ,sto (eval-args-prim ,op ,es ,vs ,env+ ,k))
     `(E ,(first es) ,env+ ,sto (eval-args-prim ,op ,(rest es) ,(append vs (list v)) ,env+ ,k))]

    ;; Calls to closures / continuing to evaluate arguments
    [`(A ,(? storable? v) ,sto (eval-args () ,vs ,env ,k))
     ;; notice the implicit canonical ordering in v-args, addrs, and xs
     (define v-args (append (rest vs) (list v)))
     (match (first vs)
       [`(clo (λ (,xs ...) ,e-b) ,env+)
        ;; allocate a new array of addresses        
        (define addrs (map (λ (x) (gensym (format "addr-~a" x))) xs))
        ;; build the new environment
        (define env++ (foldl (λ (x addr env++) (hash-set env++ x addr)) env+ xs addrs))
        ;; build the new store
        (define sto+ (foldl (λ (addr v sto+) (hash-set sto+ addr v)) sto addrs v-args))
        `(E ,e-b ,env++ ,sto+ ,k)]
       [_ (error "applied something other than a λ")])]
    ;; keep going with evaluating args
    [`(A ,(? storable? v) ,sto (eval-args ,es ,vs ,env+ ,k))
     `(E ,(first es) ,env+ ,sto (eval-args ,(rest es) ,(append vs (list v)) ,env+ ,k))]

    ;; Decide an if
    [`(A ,(? storable? v) ,sto (if-decide ,e-t ,e-f ,env+ ,k))
     (if v
         `(E ,e-t ,env+ ,sto ,k)
         `(E ,e-f ,env+ ,sto ,k))]
    [_ (error (format "unknown state ~a" (pretty-format state)))]))
    

(define (iter st)
  (match st
    [`(A ,(? storable? v) ,sto Done)
     `(result ,v ,sto)]
    [_ (pretty-print st)
       (displayln "⟼")
       (iter (step st))]))

;; examples
(iter (inj
       '(if ((λ (x y) x) #t #f)
            (prim + 1 2)
            (prim * 3 4))))

(iter (inj
       '(if
         (prim equal? 0 1)
         #t
         (((λ (f g h) (f (g h)))
           (λ (f) f)
           (λ (g) (λ (x) (g (g x))))
           (λ (x) (prim + x 1)))
          5))))
