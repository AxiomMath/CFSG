module

public import Certificates.Data.Kernel.U6.Perm

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2
open CFSG.KC.Enum (pcomp)

@[expose] noncomputable def ap5 (x i : Nat) : Nat := fget x i (nat_lit 5)

@[expose] noncomputable def pc22 (p q : Nat) : Nat :=
  strictN p fun p => strictN q fun q => pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) p q

@[expose] noncomputable def commM (r x : Nat) : Bool :=
  allN (nat_lit 22) fun i => Nat.beq (ap5 x (ap5 r i)) (ap5 r (ap5 x i))

@[expose] noncomputable def sqK (x : Nat) : Bool :=
  allN (nat_lit 22) fun i => Nat.beq (ap5 x (ap5 x i)) i

@[expose] noncomputable def isIdK (x : Nat) : Bool := allN (nat_lit 22) fun i => Nat.beq (ap5 x i) i

@[expose] noncomputable def sqMulK (s x : Nat) : Bool :=
  allN (nat_lit 22) fun i => Nat.beq (ap5 x (ap5 s (ap5 x (ap5 s i)))) i

@[expose] noncomputable def keyK (x : Nat) : Nat :=
  sumN (nat_lit 22) fun i => Nat.shiftLeft (ap5 x i) (Nat.mul (nat_lit 5) (Nat.sub (nat_lit 21) i))

@[expose] noncomputable def memK (L : List Nat) (k : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => orB (Nat.beq y k) ih) L

@[expose] noncomputable def missOutK (r : Nat) (L : List Nat) (x : Nat) : Bool :=
  andB (sqK x) (andB (commM r x) (andB (notB (isIdK x))
    (orB (notB (memK L (keyK x))) (notB (memK L (keyK (pc22 x r)))))))

@[expose] noncomputable def missInK (r : Nat) (L : List Nat) (x : Nat) : Bool :=
  andB (sqK x) (andB (commM r x) (andB (notB (isIdK x))
    (andB (notB (Nat.beq x r)) (notB (memK L (keyK x))))))

@[expose] noncomputable def ind (b : Bool) (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (pw2 (Nat.mul (nat_lit 20) k)) b

@[expose] noncomputable def cntVec (R8 R0 RY : Nat) (L8 L0 LY : List Nat) (x : Nat) : Nat :=
  Nat.add (ind (orB (missOutK R8 L8 x) (orB (missOutK R0 L0 x) (missInK RY LY x)))
      (nat_lit 0))
    (Nat.add (ind (sqMulK R8 x) (nat_lit 1))
      (Nat.add (ind (andB (sqK x) (notB (isIdK x))) (nat_lit 2))
        (Nat.add (ind (commM R8 x) (nat_lit 3))
          (Nat.add (ind (commM R0 x) (nat_lit 4)) (ind (commM RY x) (nat_lit 5))))))

@[expose] noncomputable def chunkK (R8 R0 RY : Nat) (L8 L0 LY : List Nat) (TR : Nat → Nat)
    (o a : Nat) : Nat :=
  strictN (TR (Nat.add (fget o (nat_lit 0) (nat_lit 32)) a)) fun x0 =>
  sumN (nat_lit 21) fun b => strictN (pc22 x0 (TR (Nat.add (fget o (nat_lit 1) (nat_lit 32)) b)))
    fun x1 =>
  sumN (nat_lit 20) fun c => strictN (pc22 x1 (TR (Nat.add (fget o (nat_lit 2) (nat_lit 32)) c)))
    fun x2 =>
  sumN (nat_lit 16) fun d => strictN (pc22 x2 (TR (Nat.add (fget o (nat_lit 3) (nat_lit 32)) d)))
    fun x3 =>
  sumN (nat_lit 3) fun e =>
    cntVec R8 R0 RY L8 L0 LY (pc22 x3 (TR (Nat.add (fget o (nat_lit 4) (nat_lit 32)) e)))

end CFSG.KC.U6

end
