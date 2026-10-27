module

public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.CosetLat

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def ctabAt (M : Nat → Nat → Nat) (G : Nat → Nat) (nG : Nat)
    (ET : Nat → Nat) (nT : Nat) (EU : Nat → Nat) (nU : Nat) (CR : Nat → Nat) (i : Nat) : Bool :=
  allN nG fun j => letB (CR (Nat.add (Nat.mul i nG) j)) fun r =>
    letB (Nat.land r (nat_lit 16777215)) fun k => letB (Nat.shiftRight r (nat_lit 24)) fun v =>
      andB (Nat.blt k nT) (andB (Nat.blt v nU) (Nat.beq (EU v) (M (M (ET k) (EU i)) (G j))))

@[expose] noncomputable def transAt (M : Nat → Nat → Nat) (RC : Nat → Nat) (nR : Nat)
    (ET : Nat → Nat) (nT : Nat) (EU UR : Nat → Nat) (i : Nat) : Bool :=
  letB (UR i) fun r =>
    letB (Nat.land r (nat_lit 16777215)) fun a => letB (Nat.shiftRight r (nat_lit 24)) fun e =>
      andB (Nat.blt a nR) (andB (Nat.blt e nT) (Nat.beq (EU i) (M (RC a) (ET e))))

@[expose] noncomputable def notInAt (M : Nat → Nat → Nat) (ET : Nat → Nat) (nT : Nat)
    (EU : Nat → Nat) (x a : Nat) : Bool :=
  allN nT fun k => notB (Nat.beq (M (ET k) (EU a)) x)

@[expose] noncomputable def wordG (M : Nat → Nat → Nat) (one : Nat) (A : Nat → Nat)
    (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) one (fun l _ ih => M (A l) ih) w

@[expose] noncomputable def lettersG (nA : Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun l _ ih => andB (Nat.blt l nA) ih) w

@[expose] noncomputable def wordAt (M : Nat → Nat → Nat) (one : Nat) (A : Nat → Nat) (nA : Nat)
    (w : List Nat) (c : Nat) : Bool :=
  andB (lettersG nA w) (Nat.beq (wordG M one A w) c)

end CFSG.KC.CosetLat

end
