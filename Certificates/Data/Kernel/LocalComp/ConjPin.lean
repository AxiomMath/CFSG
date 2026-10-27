module

public import Certificates.Data.Kernel.BfsPin

public section

namespace CFSG.KC.LocalComp.ConjPin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.KLie.CT (fget notB)

@[expose] noncomputable def cStep (n w m : Nat) (T : Nat → Nat) (t row g gi k c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), nat_lit 0,
    strictN (pcomp n w m g (pcomp n w m t gi)) fun y => strictN (fget row k (nat_lit 16)) fun j =>
      nIf(Nat.blt j c, nIf(Nat.beq (T j) y, c, nat_lit 0),
        nIf(Nat.beq j c, nIf(Nat.beq (T c) y, Nat.succ c, nat_lit 0), nat_lit 0)))

@[expose] noncomputable def cPoint (n w m ng : Nat) (G GI T E : Nat → Nat) (i c : Nat) : Nat :=
  strictN (T i) fun t => strictN (E i) fun row =>
    Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
      (fun r ih c => strictN (cStep n w m T t row (G (Nat.sub (Nat.sub ng r) (nat_lit 1)))
        (GI (Nat.sub (Nat.sub ng r) (nat_lit 1))) (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) ih) ng c

@[expose] noncomputable def runCK (n w m ng : Nat) (G GI T E : Nat → Nat) (N : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun r ih c => strictN (nIf(Nat.blt (Nat.sub (Nat.sub N r) (nat_lit 1)) c,
      cPoint n w m ng G GI T E (Nat.sub (Nat.sub N r) (nat_lit 1)) c, nat_lit 0)) ih) N (nat_lit 1)

@[expose] noncomputable def bfsCK (n w ng : Nat) (G GI : Nat → Nat) (X N : Nat) (T E S : Nat → Nat) :
    Bool :=
  bAnd(szOK n w,
  bAnd(allN ng (fun k => canonK n w (mask w) (Nat.mul n w) (G k)),
  bAnd(allN ng (fun k => canonK n w (mask w) (Nat.mul n w) (GI k)),
  bAnd(allN N (fun i => canonK n w (mask w) (Nat.mul n w) (T i)),
  bAnd(Nat.beq (T (nat_lit 0)) X,
  bAnd(distinctK N T S,
    Nat.beq (runCK n w (mask w) ng G GI T E N) N))))))

@[expose] noncomputable def notInK (n w N : Nat) (T : Nat → Nat) (X : Nat) : Bool :=
  bAnd(canonK n w (mask w) (Nat.mul n w) X,
    allN N fun p => bAnd(canonK n w (mask w) (Nat.mul n w) (T p), notB (Nat.beq (T p) X)))

end CFSG.KC.LocalComp.ConjPin

end
