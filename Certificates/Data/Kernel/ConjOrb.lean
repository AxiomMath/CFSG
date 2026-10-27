module

public import Certificates.Data.Kernel.BfsPinBase

public section

namespace CFSG.KC.ConjOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.KLie.CT (fget)

@[expose] noncomputable def blk (F : Nat → Nat) (bw i : Nat) : Nat :=
  fget (F (Nat.shiftRight i (nat_lit 6))) (Nat.land i (nat_lit 63)) bw

@[expose] noncomputable def pconj (n w m g gi t : Nat) : Nat := pcomp n w m g (pcomp n w m t gi)

@[expose] noncomputable def headK (n w ng : Nat) (G GI : Nat → Nat) : Bool :=
  bAnd(szOK n w, allN ng fun k => bAnd(canonK n w (mask w) (Nat.mul n w) (G k),
    bAnd(canonK n w (mask w) (Nat.mul n w) (GI k), permOK n w (mask w) (Nat.mul n w) (G k) (GI k))))

@[expose] noncomputable def closPt (n w ng N : Nat) (G GI T E : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) fun t => strictB (E i) fun row =>
    bAnd(canonK n w (mask w) (Nat.mul n w) t,
      allN ng fun k => strictB (fget row k (nat_lit 20)) fun j =>
        bAnd(Nat.blt j N, Nat.beq (pconj n w (mask w) (G k) (GI k) t) (T j)))

@[expose] noncomputable def tPar (d : Nat) : Nat := Nat.land d (nat_lit 1048575)

@[expose] noncomputable def tLab (d : Nat) : Nat := Nat.land (Nat.shiftRight d (nat_lit 20)) (nat_lit 15)

@[expose] noncomputable def tDep (d : Nat) : Nat := Nat.shiftRight d (nat_lit 24)

@[expose] noncomputable def treePt (ng N r : Nat) (E D : Nat → Nat) (i : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (strictB (D i) fun d =>
      bAnd(Nat.blt (tPar d) N, bAnd(Nat.blt (tLab d) ng,
        bAnd(Nat.beq (fget (E (tPar d)) (tLab d) (nat_lit 20)) i,
          Nat.beq (Nat.succ (tDep (D (tPar d)))) (tDep d)))))
    true (Nat.beq i r)

end CFSG.KC.ConjOrb

end
