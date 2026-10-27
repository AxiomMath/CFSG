module

public import Certificates.Data.Kernel.BfsPinSlice
public import Certificates.Data.Kernel.PGrp

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.PGrp
open CFSG.KLie.CT (fget)

@[expose] noncomputable def genStepY (n w N : Nat) (ps : List Nat) (T : Nat → Nat)
    (t row g k c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), nat_lit 0,
    strictN (fget row k (nat_lit 16)) fun j =>
      nIf(Nat.blt j c,
        nIf(bAnd(Nat.blt j N, Nat.beq (keyCK n w ps g t) (keyK n w ps (T j))), c, nat_lit 0),
        nIf(Nat.beq j c, nIf(Nat.beq (T c) (pcomp n w (mask w) g t), Nat.succ c, nat_lit 0),
          nat_lit 0)))

@[expose] noncomputable def pointStepY (n w ng N : Nat) (ps : List Nat) (G T E : Nat → Nat)
    (i c : Nat) : Nat :=
  strictN (T i) fun t => strictN (E i) fun row =>
    Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
      (fun r ih c => strictN (genStepY n w N ps T t row (G (Nat.sub (Nat.sub ng r) (nat_lit 1)))
        (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) ih) ng c

@[expose] noncomputable def runFY (n w ng N : Nat) (ps : List Nat) (G T E : Nat → Nat)
    (len : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun _ ih lo c => strictN (nIf(Nat.blt lo c, pointStepY n w ng N ps G T E lo c, nat_lit 0))
      (ih (Nat.succ lo))) len

@[expose] noncomputable def runSlY (n w ng N : Nat) (ps : List Nat) (G T E : Nat → Nat) (L : Nat)
    (C : Nat → Nat) (s : Nat) : Bool :=
  Nat.beq (runFY n w ng N ps G T E L (Nat.mul L s) (C s)) (C (Nat.succ s))

end CFSG.KC.BfsPin

end
