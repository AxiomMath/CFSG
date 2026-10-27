module

public import CFSG.Certificates.Kernel.LieCocycle.Fi22.Core

public section

namespace CFSG.KS.RuTree

open CFSG.KLC.Fi22

@[expose] noncomputable def R2 : Nat := Nat.add (nat_lit 1) (Nat.shiftLeft (nat_lit 1) (nat_lit 4096))

@[expose] noncomputable def mv (N0 N1 e x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (applyNW N0 R2 x) (applyNW N1 R2 x)
    (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def hk (x : Nat) : Nat :=
  Nat.mod (Nat.shiftRight x (nat_lit 4096)) (nat_lit 2305843009213693951)

@[expose] noncomputable def tabK (F : Nat → Nat) (w i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (F (Nat.shiftRight i (nat_lit 4))) (Nat.mul w (Nat.land i (nat_lit 15))))
    (maskN w)

@[expose] noncomputable def slotK (D : Nat → Nat) (M B h : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.mod (Nat.shiftRight h (nat_lit 20)) M) (tabK D (nat_lit 16) (Nat.mod h B))) M

@[expose] noncomputable def chkK (T D : Nat → Nat) (M B j x : Nat) : Bool :=
  Nat.beq (tabK T (nat_lit 20) (slotK D M B (hk x))) j

@[expose] noncomputable def ndK (FC : Nat → Nat) (j : Nat) : Nat :=
  Nat.land (Nat.shiftRight (FC (Nat.shiftRight j (nat_lit 4)))
    (Nat.add (nat_lit 20) (Nat.mul (nat_lit 9) (Nat.land j (nat_lit 15))))) (nat_lit 511)

@[expose] noncomputable def fcK (FC : Nat → Nat) (j : Nat) : Nat :=
  Nat.add (Nat.land (FC (Nat.shiftRight j (nat_lit 4))) (nat_lit 1048575))
    (Nat.land (ndK FC j) (nat_lit 63))

@[expose] noncomputable def ncK (FC : Nat → Nat) (j : Nat) : Nat :=
  Nat.land (Nat.shiftRight (ndK FC j) (nat_lit 6)) (nat_lit 3)

@[expose] noncomputable def cutK (FC : Nat → Nat) (j : Nat) : Bool :=
  Nat.beq (Nat.shiftRight (ndK FC j) (nat_lit 8)) (nat_lit 1)

@[expose] noncomputable def rngK (a n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB (f (Nat.add a k)) ih) n

@[expose] noncomputable def visitK (N0 N1 : Nat) (PL FC T D : Nat → Nat) (M B : Nat) (f : Nat) :
    Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun _ ih j x => andB (chkK T D M B j x)
      (rngK (fcK FC j) (ncK FC j) (fun c => (fun pl =>
        andB (Nat.beq (Nat.shiftRight pl (nat_lit 4)) j)
          (andB (Nat.blt (Nat.land pl (nat_lit 15)) (nat_lit 2))
            (Bool.rec (motive := fun _ => Bool) (ih c (mv N0 N1 pl x)) true (cutK FC c))))
        (PL c))))
    f

@[expose] noncomputable def udK (N0 N1 F0 : Nat) (PL : Nat → Nat) (f : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun c => Bool.rec (motive := fun _ => Nat) (nat_lit 0) F0 (Nat.beq c (nat_lit 0)))
    (fun _ ih c => Bool.rec (motive := fun _ => Nat)
      ((fun pl => mv N0 N1 pl (ih (Nat.shiftRight pl (nat_lit 4)))) (PL c)) F0 (Nat.beq c (nat_lit 0)))
    f

@[expose] noncomputable def rootK (N0 N1 F0 : Nat) (PL FC T D : Nat → Nat) (M B r : Nat) : Bool :=
  (fun u => andB (Nat.blt (nat_lit 0) (Nat.shiftRight u (nat_lit 4096)))
      (visitK N0 N1 PL FC T D M B (nat_lit 45) r u))
    (udK N0 N1 F0 PL (nat_lit 45) r)

@[expose] noncomputable def blockK (N0 N1 F0 : Nat) (PL FC T D : Nat → Nat) (M B a n : Nat) : Bool :=
  rngK a n (fun r => Bool.rec (motive := fun _ => Bool) true (rootK N0 N1 F0 PL FC T D M B r)
    (cutK FC r))

@[expose] noncomputable def partK (FC : Nat → Nat) (j : Nat) : Bool :=
  andB (Nat.beq (fcK FC (Nat.succ j)) (Nat.add (fcK FC j) (ncK FC j)))
    (orB (Nat.beq (ncK FC j) (nat_lit 0)) (Nat.blt j (fcK FC j)))

@[expose] noncomputable def isNilK (cs : List Char) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) cs

end CFSG.KS.RuTree

end
