module

public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.LQT.R

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def ent (x k : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul 2 k)) 3

@[expose] noncomputable def mk9 (g : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Nat.add acc (Nat.shiftLeft (g k) (Nat.mul 2 k))) 9

@[expose] noncomputable def mulK (x y : Nat) : Nat :=
  mk9 fun k => CFSG.KC.Loop.strictN (Nat.div k 3) fun i => CFSG.KC.Loop.strictN (Nat.mod k 3) fun j =>
    Nat.mod (Nat.add (Nat.add (Nat.mul (ent x (Nat.mul 3 i)) (ent y j))
      (Nat.mul (ent x (Nat.add (Nat.mul 3 i) 1)) (ent y (Nat.add 3 j))))
      (Nat.mul (ent x (Nat.add (Nat.mul 3 i) 2)) (ent y (Nat.add 6 j)))) 3

@[expose] noncomputable def minor (x p q r s : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.mul (ent x p) (ent x q)) (Nat.mul 2 (Nat.mul (ent x r) (ent x s)))) 3

@[expose] noncomputable def cofIdx (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat)
  (Bool.rec (motive := fun _ => Nat) 0x03010400 0x05000302 (Nat.beq k 7))
    0x04020501 (Nat.beq k 6))
    0x07000601 (Nat.beq k 5))
    0x06020800 (Nat.beq k 4))
    0x08010702 (Nat.beq k 3))
    0x06040703 (Nat.beq k 2))
    0x08030605 (Nat.beq k 1))
    0x07050804 (Nat.beq k 0)

@[expose] noncomputable def cofK (x : Nat) : Nat :=
  mk9 fun k => CFSG.KC.Loop.strictN (cofIdx k) fun q =>
    minor x (Nat.land q 255) (Nat.land (Nat.shiftRight q 8) 255) (Nat.land (Nat.shiftRight q 16) 255)
      (Nat.shiftRight q 24)

@[expose] noncomputable def detK (x : Nat) : Nat :=
  Nat.mod (Nat.add
    (Nat.add (Nat.add (Nat.mul (ent x 0) (Nat.mul (ent x 4) (ent x 8)))
      (Nat.mul (ent x 1) (Nat.mul (ent x 5) (ent x 6)))) (Nat.mul (ent x 2) (Nat.mul (ent x 3) (ent x 7))))
    (Nat.mul 2 (Nat.add (Nat.add (Nat.mul (ent x 0) (Nat.mul (ent x 5) (ent x 7)))
      (Nat.mul (ent x 1) (Nat.mul (ent x 3) (ent x 8)))) (Nat.mul (ent x 2) (Nat.mul (ent x 4) (ent x 6))))))
    3

@[expose] noncomputable def oneK : Nat := 65793

@[expose] noncomputable def pwK (x n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) oneK (fun _ acc => mulK x acc) n

@[expose] noncomputable def ofIdx (n : Nat) : Nat :=
  mk9 fun k => Nat.mod (Nat.div n (Nat.pow 3 k)) 3

@[expose] noncomputable def allSL (f : Nat → Bool) : Bool :=
  allN 19683 fun n => letB (ofIdx n) fun x => impB (Nat.beq (detK x) 1) (f x)

@[expose] noncomputable def anySL (f : Nat → Bool) : Bool :=
  anyN 19683 fun n => letB (ofIdx n) fun x => andB (Nat.beq (detK x) 1) (f x)

@[expose] noncomputable def allSLc (c : Nat) (f : Nat → Bool) : Bool :=
  allN 1024 fun i => letB (Nat.add (Nat.mul 1024 c) i) fun n => impB (Nat.blt n 19683)
    (letB (ofIdx n) fun x => impB (Nat.beq (detK x) 1) (f x))

@[expose] noncomputable def cntSL : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun n acc => Nat.add acc
    (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq (detK (ofIdx n)) 1))) 19683

@[expose] noncomputable def slOK (x : Nat) : Bool :=
  andB (Nat.blt x 262144) (andB (allN 9 fun k => Nat.blt (ent x k) 3) (Nat.beq (detK x) 1))

end CFSG.KC.LQT.R

end
