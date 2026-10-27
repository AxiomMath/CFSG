module

public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.Kernel.ConjOrb

public section

namespace CFSG.KC.PermWit

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KLie.CT (fget)

@[expose] noncomputable def siftR (n w : Nat) (LR TRI : Nat → Nat) (BP nb G : Nat) : Bool :=
  Nat.beq (Nat.shiftRight G (Nat.mul n w)) (nat_lit 0) &&
    allN n (fun i => Nat.blt (pg w (mask w) G i) n) &&
    siftK n w (mask w) (Nat.mul n w) (pidn n w) LR TRI BP nb (nat_lit 0) G

@[expose] noncomputable def cntK (N : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc fun a => Bool.rec (motive := fun _ => Nat) a (Nat.succ a) (f i)) N

@[expose] noncomputable def ordWitPt (n w p X N : Nat) (T W : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) fun t =>
    !(Nat.beq (ppow n w (mask w) (pidn n w) t p) (pidn n w)) || Nat.beq t (pidn n w) ||
      strictB (W i) fun j =>
        Nat.blt j N && Nat.beq (pcomp n w (mask w) (T j) t) (pcomp n w (mask w) X (T j))

@[expose] noncomputable def cPar (d : Nat) : Nat := Nat.land (Nat.shiftRight d (nat_lit 6)) (nat_lit 63)

@[expose] noncomputable def cLab (d : Nat) : Nat := Nat.land d (nat_lit 63)

@[expose] noncomputable def cDep (d : Nat) : Nat := Nat.shiftRight d (nat_lit 12)

@[expose] noncomputable def ctreePt (n w N k : Nat) (T : Nat → Nat) (row i : Nat) : Bool :=
  Nat.beq i (nat_lit 0) ||
    strictB (fget row i (nat_lit 16)) fun d =>
      Nat.blt (cLab d) N && Nat.blt (cPar d) N &&
        Nat.beq (Nat.succ (cDep (fget row (cPar d) (nat_lit 16)))) (cDep d) &&
        Nat.beq (T i) (pcomp n w (mask w)
          (CFSG.KC.ConjOrb.pconj n w (mask w) (T (cLab d)) (pinvS n w (mask w) (T (cLab d))) (T k))
          (T (cPar d)))

end CFSG.KC.PermWit

end
