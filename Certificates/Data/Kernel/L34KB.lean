module

public import Certificates.Data.Kernel.L34K

public section

namespace CFSG.KC.L34K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.KLie.CT (fget andB)

@[expose] noncomputable def baseEqL (w m : Nat) (G : Nat → Nat) (B : List Nat) (k t y : Nat) :
    Bool :=
  strictB (G k) fun g => List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (pg w m y b) (pg w m g (pg w m t b)), ih)) B

@[expose] noncomputable def genStepB (st : Nat → Nat → Nat) (eqb : Nat → Nat → Nat → Bool)
    (T : Nat → Nat) (ew t row k c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), nat_lit 0,
    strictN (fget row k ew) fun j =>
      nIf(Nat.blt j c, nIf(eqb k t (T j), c, nat_lit 0),
        nIf(Nat.beq j c, nIf(Nat.beq (T c) (st k t), Nat.succ c, nat_lit 0), nat_lit 0)))

@[expose] noncomputable def pointStepB (ng : Nat) (st : Nat → Nat → Nat)
    (eqb : Nat → Nat → Nat → Bool) (T E : Nat → Nat) (ew i c : Nat) : Nat :=
  strictN (T i) fun t => strictN (E i) fun row =>
    Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
      (fun r ih c => strictN (genStepB st eqb T ew t row (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) ih)
      ng c

@[expose] noncomputable def runFB (ng : Nat) (st : Nat → Nat → Nat) (eqb : Nat → Nat → Nat → Bool)
    (T E : Nat → Nat) (ew : Nat) (len : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun _ ih lo c => strictN (nIf(Nat.blt lo c, pointStepB ng st eqb T E ew lo c, nat_lit 0))
      (ih (Nat.succ lo))) len

@[expose] noncomputable def runSlB (ng : Nat) (st : Nat → Nat → Nat) (eqb : Nat → Nat → Nat → Bool)
    (T E : Nat → Nat) (ew L : Nat) (C : Nat → Nat) (s : Nat) : Bool :=
  Nat.beq (runFB ng st eqb T E ew L (Nat.mul L s) (C s)) (C (Nat.succ s))

@[expose] noncomputable def pinSlB (n w m ng : Nat) (G T E C S SI : Nat → Nat) (B : List Nat)
    (N L ew s : Nat) : Bool :=
  andB (runSlB ng (lstep n w G) (baseEqL w m G B) T E ew L C s) (distSl N T S SI L s)

end CFSG.KC.L34K

end
