module

public import CFSG.Certificates.Kernel.Orders.Mat

public section

namespace CFSG.KC.C7153

open CFSG.KC.Ord CFSG.KC.Loop

@[expose] noncomputable def fA (x y : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.add (Nat.mod x 5) (Nat.mod y 5)) 5)
    (Nat.mul 5 (Nat.mod (Nat.add (Nat.mod (Nat.div x 5) 5) (Nat.mod (Nat.div y 5) 5)) 5))

@[expose] noncomputable def fM (x y : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.add (Nat.mul (Nat.mod x 5) (Nat.mod y 5))
      (Nat.mul (Nat.mul 2 (Nat.mod (Nat.div x 5) 5)) (Nat.mod (Nat.div y 5) 5))) 5)
    (Nat.mul 5 (Nat.mod (Nat.add (Nat.mul (Nat.mod x 5) (Nat.mod (Nat.div y 5) 5))
      (Nat.mul (Nat.mod (Nat.div x 5) 5) (Nat.mod y 5))) 5))

@[expose] noncomputable def fC (x : Nat) : Nat :=
  Nat.add (Nat.mod x 5) (Nat.mul 5 (Nat.mod (Nat.sub 5 (Nat.mod (Nat.div x 5) 5)) 5))

@[expose] noncomputable def fN (x : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.sub 5 (Nat.mod x 5)) 5)
    (Nat.mul 5 (Nat.mod (Nat.sub 5 (Nat.mod (Nat.div x 5) 5)) 5))

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) n

@[expose] noncomputable def letB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def ent (M s : Nat) : Nat := Nat.land (Nat.shiftRight M s) 31

@[expose] noncomputable def pk9 (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat) : Nat :=
  Nat.lor x0 (Nat.lor (Nat.shiftLeft x1 5) (Nat.lor (Nat.shiftLeft x2 10)
    (Nat.lor (Nat.shiftLeft x3 15) (Nat.lor (Nat.shiftLeft x4 20) (Nat.lor (Nat.shiftLeft x5 25)
      (Nat.lor (Nat.shiftLeft x6 30) (Nat.lor (Nat.shiftLeft x7 35) (Nat.shiftLeft x8 40))))))))

@[expose] noncomputable def idM : Nat := pk9 1 0 0 0 1 0 0 0 1

@[expose] noncomputable def mul9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 b0 b1 b2 b3 b4 b5 b6 b7 b8 : Nat) :
    Nat :=
  pk9 (fA (fA (fM a0 b0) (fM a1 b3)) (fM a2 b6)) (fA (fA (fM a0 b1) (fM a1 b4)) (fM a2 b7))
    (fA (fA (fM a0 b2) (fM a1 b5)) (fM a2 b8)) (fA (fA (fM a3 b0) (fM a4 b3)) (fM a5 b6))
    (fA (fA (fM a3 b1) (fM a4 b4)) (fM a5 b7)) (fA (fA (fM a3 b2) (fM a4 b5)) (fM a5 b8))
    (fA (fA (fM a6 b0) (fM a7 b3)) (fM a8 b6)) (fA (fA (fM a6 b1) (fM a7 b4)) (fM a8 b7))
    (fA (fA (fM a6 b2) (fM a7 b5)) (fM a8 b8))

@[expose] noncomputable def mulM (A B : Nat) : Nat :=
  strictN A fun A => strictN B fun B =>
    mul9 (ent A 0) (ent A 5) (ent A 10) (ent A 15) (ent A 20) (ent A 25) (ent A 30) (ent A 35)
      (ent A 40) (ent B 0) (ent B 5) (ent B 10) (ent B 15) (ent B 20) (ent B 25) (ent B 30)
      (ent B 35) (ent B 40)

@[expose] noncomputable def cT (A : Nat) : Nat :=
  strictN A fun A =>
    pk9 (fC (ent A 0)) (fC (ent A 15)) (fC (ent A 30)) (fC (ent A 5)) (fC (ent A 20))
      (fC (ent A 35)) (fC (ent A 10)) (fC (ent A 25)) (fC (ent A 40))

@[expose] noncomputable def det9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Nat) : Nat :=
  fA (fA (fM a0 (fA (fM a4 a8) (fN (fM a5 a7))))
    (fN (fM a1 (fA (fM a3 a8) (fN (fM a5 a6))))))
    (fM a2 (fA (fM a3 a7) (fN (fM a4 a6))))

@[expose] noncomputable def det3 (A : Nat) : Nat :=
  strictN A fun A =>
    det9 (ent A 0) (ent A 5) (ent A 10) (ent A 15) (ent A 20) (ent A 25) (ent A 30) (ent A 35)
      (ent A 40)

@[expose] noncomputable def pow5 (A : Nat) : Nat :=
  strictN (mulM A A) fun A2 => strictN (mulM A2 A2) fun A4 => mulM A4 A

@[expose] noncomputable def rng9 (M : Nat) : Bool :=
  andB (Nat.blt (ent M 0) 25) (andB (Nat.blt (ent M 5) 25) (andB (Nat.blt (ent M 10) 25)
    (andB (Nat.blt (ent M 15) 25) (andB (Nat.blt (ent M 20) 25) (andB (Nat.blt (ent M 25) 25)
      (andB (Nat.blt (ent M 30) 25) (andB (Nat.blt (ent M 35) 25) (Nat.blt (ent M 40) 25))))))))

@[expose] noncomputable def suK (A : Nat) : Bool :=
  andB (Nat.beq (mulM (cT A) A) idM) (Nat.beq (det3 A) 1)

@[expose] noncomputable def yOf (k : Nat) : Nat :=
  pk9 (Nat.div k 25) (fN (fC (Nat.mod k 25))) 0 (Nat.mod k 25) (fC (Nat.div k 25)) 0 0 0 1

@[expose] noncomputable def memK (W : List Nat) (k : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun r _ ih => orB (Nat.beq (Nat.land r 1023) k) ih) W

@[expose] noncomputable def caseAC (W : List Nat) (a c : Nat) : Bool :=
  orB (notB (Nat.beq (fA (fM a (fC a)) (fM c (fC c))) 1))
    (letB (yOf (Nat.add (Nat.mul 25 a) c)) fun y =>
      orB (notB (andB (Nat.beq (pow5 y) idM) (notB (Nat.beq y idM))))
        (memK W (Nat.add (Nat.mul 25 a) c)))

@[expose] noncomputable def walkAC (W : List Nat) : Bool :=
  allN 25 fun a => allN 25 fun c => caseAC W a c

@[expose] noncomputable def witAB (y A B : Nat) : Bool :=
  andB (suK A) (andB (suK B) (andB (Nat.beq (mulM A B) (mulM (mulM y B) A))
    (andB (Nat.beq (mulM A y) (mulM y A)) (andB (Nat.beq (mulM B y) (mulM y B))
      (andB (Nat.beq (pow5 A) idM) (Nat.beq (pow5 B) idM))))))

@[expose] noncomputable def witG (r : Nat) : Bool :=
  letB (Nat.land r 1023) fun k => letB (Nat.land (Nat.shiftRight r 10) 35184372088831) fun A =>
    letB (Nat.shiftRight r 55) fun B =>
      andB (Nat.blt k 625) (andB (Nat.blt B 35184372088832) (andB (rng9 A) (andB (rng9 B)
        (letB (yOf k) fun y => witAB y A B))))

@[expose] noncomputable def witsG (W : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih => andB (witG r) ih) W

@[expose] noncomputable def c7153K (W : List Nat) : Bool := andB (walkAC W) (witsG W)

end CFSG.KC.C7153

end
