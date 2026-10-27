module

public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.KLie.CT (fget orN pw2 maskN)

@[expose] noncomputable def genStep (n w m : Nat) (T : Nat → Nat) (t row g k c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), nat_lit 0,
    strictN (pcomp n w m g t) fun y => strictN (fget row k (nat_lit 16)) fun j =>
      nIf(Nat.blt j c, nIf(Nat.beq (T j) y, c, nat_lit 0),
        nIf(Nat.beq j c, nIf(Nat.beq (T c) y, Nat.succ c, nat_lit 0), nat_lit 0)))

@[expose] noncomputable def pointStep (n w m ng : Nat) (G T E : Nat → Nat) (i c : Nat) : Nat :=
  strictN (T i) fun t => strictN (E i) fun row =>
    Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
      (fun r ih c => strictN (genStep n w m T t row (G (Nat.sub (Nat.sub ng r) (nat_lit 1)))
        (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) ih) ng c

@[expose] noncomputable def runK (n w m ng : Nat) (G T E : Nat → Nat) (N : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun r ih c => strictN (nIf(Nat.blt (Nat.sub (Nat.sub N r) (nat_lit 1)) c,
      pointStep n w m ng G T E (Nat.sub (Nat.sub N r) (nat_lit 1)) c, nat_lit 0)) ih) N (nat_lit 1)

@[expose] noncomputable def distinctK (N : Nat) (T S : Nat → Nat) : Bool :=
  bAnd(allN (Nat.sub N (nat_lit 1)) (fun k => Nat.blt (T (S k)) (T (S (Nat.succ k)))),
    bAnd(allN N (fun k => Nat.blt (S k) N),
      Nat.beq (orN N fun k => pw2 (S k)) (maskN N)))

@[expose] noncomputable def packA (w : Nat) (a : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ acc => Nat.lor x (Nat.shiftLeft acc w)) a

@[expose] noncomputable def bfsK (n w ng : Nat) (G : Nat → Nat) (N : Nat) (T E S : Nat → Nat) :
    Bool :=
  bAnd(szOK n w,
  bAnd(allN ng (fun k => canonK n w (mask w) (Nat.mul n w) (G k)),
  bAnd(allN N (fun i => canonK n w (mask w) (Nat.mul n w) (T i)),
  bAnd(Nat.beq (T (nat_lit 0)) (pidn n w),
  bAnd(distinctK N T S,
    Nat.beq (runK n w (mask w) ng G T E N) N)))))

end CFSG.KC.BfsPin

end
