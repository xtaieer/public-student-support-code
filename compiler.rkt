#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require racket/dict)
(require "interp.rkt")
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "utilities.rkt")
(require "type-check-Cvar.rkt")

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

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (let* ([new-name (gensym)] [new-env (dict-set env x new-name)]) (Let new-name ((uniquify-exp env) e) ((uniquify-exp new-env) body)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

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
  [(Prim op args) (let-values ([(var-atoms new-args) (rco-exp-list '() args)]) (rebuild-prim-exp var-atoms op new-args))]
  [(Let var e b) (Let var (rco-exp e) (rco-exp b))]))

(define (rebuild-prim-exp var-atoms op args)
  (match var-atoms
    ['() (Prim op args)]
    [(cons va tail) (Let (car va) (cdr va) (rebuild-prim-exp tail op args))]))

(define (rco-exp-list var-atoms exps)
  (match exps
    ['() (values var-atoms '())]
    [(cons e tail)
     (let-values ([(new-var-atoms new-tail) (rco-exp-list var-atoms tail)])
       (if (atom? e)
           (values new-var-atoms (cons e new-tail))
           (let ([var-atom (rco-atom e)]) (values (cons var-atom new-var-atoms) (cons (Var (car var-atom)) new-tail)))))]))

(define (rco-atom exp) (cons (gensym) (rco-exp exp)))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info body) (type-check-Cvar (CProgram info (dict-set '() 'start (explicate-tail body))))]))

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
    [(CProgram info alist) (X86Program info (append (for/list ([a alist]) (cons (car a) (Block info (select-instructions-tail (cdr a) 'conclusion)))) (list (cons 'conclusion (Block '() (list (Retq)))))))]))

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
       [(Int n) (list (Instr 'movq (list (Imm n) (Var x))))]
       [(Var v) (list (Instr 'movq (list (Var v) (Var x))))]
       [(Prim '- (list e)) (list (Instr 'movq (list (select-instructions-atom e) (Var x))) (Instr 'negq (list (Var x))))]
       [(Prim '+ (list e1 e2)) (list (Instr 'movq (list (select-instructions-atom e1) (Var x))) (Instr 'addq (list (select-instructions-atom e2) (Var x))))]
       [(Prim 'read '()) (list (Callq 'read_int) (Instr 'movq (list (Reg 'rax) (Var x))))])]))
    
(define (select-instructions-atom a)
  (match a
    [(Var v) (Var v)]
    [(Int n) (Imm n)]))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (match p
    [(X86Program info label-blocks) (let-values ([(env pos new-blocks) (assign-homes-blocks '() 0 label-blocks)]) (X86Program (cons 'stack-space pos) new-blocks))]))

(define (assign-homes-block env stack-pos block)
  (match block
    [(Block info instrs) (let-values ([(new-env new-pos new-instrs) (assign-homes-instrs env stack-pos instrs)]) (values new-env new-pos (Block info new-instrs)))]))

(define (assign-homes-blocks env stack-pos label-blocks)
  (match label-blocks
    ['() (values env stack-pos '())]
    [(cons label-block tail)
     (let*-values ([(new-env new-pos new-block) (assign-homes-block env stack-pos (cdr label-block))] [(env2 pos2 new-tail) (assign-homes-blocks new-env new-pos tail)])
       (values env2 pos2 (cons (cons (car label-block) new-block) new-tail)))]))

(define (assign-homes-instrs env stack-pos instr-list)
  (match instr-list
    ['() (values env stack-pos '())]
    [(cons instr tail) (let*-values ([(env1 pos1 new-instr) (assign-homes-instr env stack-pos instr)] [(env2 pos2 new-tail) (assign-homes-instrs env1 pos1 tail)]) (values env2 pos2 (cons new-instr new-tail)))]))

(define (assign-homes-instr env stack-pos instr)
  (match instr
    [(Instr 'negq (list a)) (let-values ([(new-env new-stack-pos new-instr) (assign-homes-arg env stack-pos a)]) (values new-env new-stack-pos (Instr 'negq (list new-instr))))]
    [(Instr op (list e1 e2)) (let*-values ([(env1 pos1 instr1) (assign-homes-arg env stack-pos e1)] [(env2 pos2 instr2) (assign-homes-arg env1 pos1 e2)]) (values env2 pos2 (Instr op (list instr1 instr2))))]
    [else (values env stack-pos instr)]))

(define (assign-homes-arg env stack-pos a)
  (match a
    [(Imm i) (values env stack-pos (Imm i))]
    [(Reg r) (values env stack-pos (Reg r))]
    [(Var v)
     (if (dict-has-key? env v)
         (values env stack-pos (Deref 'rbp (dict-ref env v)))
         (let* ([new-stack-pos (+ stack-pos 8)] [new-env (dict-set env v new-stack-pos)]) (values new-env new-stack-pos (Deref 'rbp new-stack-pos))))]))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(X86Program info label-blocks)
     (X86Program
      info
      (map
       (lambda (label-block)
         (cons (car label-block)
               (match (cdr label-block) [(Block info instrs) (Block info (foldr append '() (map patch-instructions-instr instrs)))])))
       label-blocks))]))

(define (patch-instructions-instr instr)
  (match instr
    [(Instr 'movq (list (Deref reg1 int1) (Deref reg2 int2))) (list (Instr 'movq (list (Deref reg1 int1) (Reg 'rax))) (Instr 'movq (list (Reg 'rax) (Deref reg2 int2))))]
    [else (list instr)]))

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
     ("assign homes" ,assign-homes ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

