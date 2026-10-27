module

public import Certificates.Data.Kernel.U6.Perm

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2

@[expose] noncomputable def subP (A m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ID693
    (fun i acc => strictN acc fun acc =>
      nIf(Nat.beq (fget m i (nat_lit 1)) (nat_lit 1), pc (elt A i) acc, acc))
    (nat_lit 9)

@[expose] noncomputable def subImg (A m x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x
    (fun i y => strictN y fun y =>
      nIf(Nat.beq (fget m i (nat_lit 1)) (nat_lit 1), ap10 (elt A i) y, y))
    (nat_lit 9)

@[expose] noncomputable def abarK (A : Nat) : Bool :=
  andB (allN (nat_lit 9) fun i => strictB (elt A i) fun a =>
      andB (notB (Nat.beq a ID693)) (Nat.beq (pc a a) ID693))
    (andB (allN (nat_lit 9) fun i => allN (nat_lit 9) fun j =>
        Nat.beq (pc (elt A i) (elt A j)) (pc (elt A j) (elt A i)))
      (allN (nat_lit 511) fun m =>
        orB (notB (Nat.beq (subImg A (Nat.succ m) (nat_lit 1)) (nat_lit 1)))
          (orB (notB (Nat.beq (subImg A (Nat.succ m) (nat_lit 3)) (nat_lit 3)))
            (notB (Nat.beq (subImg A (Nat.succ m) (nat_lit 45)) (nat_lit 45))))))

@[expose] noncomputable def conjK (A P M n : Nat) : Bool :=
  allN n fun k => strictB (elt P k) fun p => strictB (invP p) fun q =>
    allN (nat_lit 9) fun i =>
      Nat.beq (pc (pc p (elt A i)) q)
        (subP A (fget M (Nat.add (Nat.mul (nat_lit 9) k) i) (nat_lit 9)))

@[expose] noncomputable def wordsK (S P : Nat) (W : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih i => andB (Nat.beq (elt P i) (evW S w)) (ih (Nat.succ i))) W (nat_lit 0)

end CFSG.KC.U6

end
