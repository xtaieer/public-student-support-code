#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp.rkt")
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "utilities.rkt")

(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (define new-name (gensym)) (define new-env (dict-set env x new-name)) (Let new-name ((uniquify-exp env) e) ((uniquify-exp new-env) body))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info exp) (Program info (rco-exp exp))]))

(define (atom? exp)
  (match exp
    [(Int v) #t]
    [(Var v) #t]
    [else #f]))

(define (rco-exp exp)
  (match exp
  [(Int v) (Int v)]
  [(Var v) (Var v)]
  [(Prim 'read '()) (Prim 'read '())]
  [(Prim '- (list e))
   (if (atom? e)
       (Prim '- (list e))
       (let-values ([(var-name dict) (rco-atom e)]) (Let var-name (dict-ref dict var-name) (Prim '- (list (Var var-name))))))]
  [(Prim '+ (list e1 e2))
   (match (list (atom? e1) (atom? e2))
     [(list #t #t) (Prim '+ (list e1 e2))]
     [(list #f #f)
      (define-values (name1 alist1) (rco-atom e1))
      (define-values (name2 alist2) (rco-atom e2))
      (Let name1 (dict-ref alist1 name1) (Let name2 (dict-ref alist2 name2) (Prim '+ (list (Var name1) (Var name2)))))]
     [(list #f #t) (define-values (name1 alist1) (rco-atom e1)) (Let name1 (dict-ref alist1 name1) (Prim '+ (list (Var name1) e2)))]
     [(list #t #f) (define-values (name2 alist2) (rco-atom e2)) (Let name2 (dict-ref alist2 name2) (Prim '+ (list e1 (Var name2))))])]
  [(Let var e b) (Let var (rco-exp e) (rco-exp b))]))

(define (rco-atom exp)
 (define var-name (gensym))
  (values var-name (dict-set '() var-name (rco-exp exp))))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info body) (CProgram info (dict-set '() 'start (explicate-tail body)))]))

(define (explicate-tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let x rhs body) (explicate-assign rhs x (explicate-tail body))]
    [(Prim op es) (Return (Prim op es))]
    [else (error "explicate-tail unhandled case" e)]))

(define (explicate-assign e x cont)
  (match e
    [(Var v) (Seq (Assign (Var x) (Var v)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body)
     (define tail (explicate-assign rhs y (explicate-tail body)))
     (assign-tail tail x cont)]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [else (error "explicate-assign unhandled case" e)]))

(define (assign-tail tail x cont)
  (match tail
    [(Return exp) (Seq (Assign (Var x) exp) cont)]
    [(Seq st ta) (Seq st (assign-tail ta x cont))]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info alist) (X86Program info  (for/list ([a alist]) (cons (car a) (Block info (select-instructions-tail (cdr a) (car a))))))]))

(define (select-instructions-tail tail label)
  (match tail
    [(Return exp)
     (match exp
       [(Var v) (list (Instr 'movq (list (Var v) (Reg 'rax))) (Jmp label))]
       [(Int n) (list (Instr 'movq (list (Imm n) (Reg 'rax))) (Jmp label))]
       [(Prim '- (list e)) (list (Instr 'movq (list (select-instructions-atom e) (Reg 'rax))) (Instr 'negq (list (Reg 'rax))) (Jmp label))]
       [(Prim '+ (list e1 e2)) (list (Instr 'movq (list (select-instructions-atom e1) (Reg 'rax))) (Instr 'addq (list (select-instructions-atom e2) (Reg 'rax))) (Jmp label))]
       [(Prim 'read '()) (list (Callq 'read_int) (Jmp label))])]
    [(Seq stmt t) (append (select-instructions-assgin stmt) (select-instructions-tail t label))]))

(define (select-instructions-assgin assgin)
  (match assgin
    [(Assign (Var x) exp)
     (match exp
       [(Prim '- (list e)) (list (Instr 'movq (list (select-instructions-atom e) (Var x))) (Instr 'negq (list (Var x))))]
       [(Prim '+ (list e1 e2)) (list (Instr 'movq (list (select-instructions-atom e1) (Var x))) (Instr 'addq (list (select-instructions-atom e2) (Var x))))]
       [(Prim 'read '()) (list (Callq 'read_int) (Instr 'movq (list (Reg 'rax) (Var x))))])]))
    
(define (select-instructions-atom a)
  (match a
    [(Var v) (Var v)]
    [(Int n) (Imm n)]))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("uniquify" ,uniquify ,interp-Lvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar)
     ("instruction selection" ,select-instructions ,interp-x86-0)
     ;; ("assign homes" ,assign-homes ,interp-x86-0)
     ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

