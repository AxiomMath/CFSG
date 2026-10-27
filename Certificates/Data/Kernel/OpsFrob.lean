module

public import Certificates.Data.Kernel.OpsV4
public import Certificates.Data.ONFrobenius

public section

namespace CFSG.KC.OpsFrob

open CFSG.SectionRank.Native CFSG.KC.OpsK CFSG.KC.LQT CFSG.KC.OpsLayK CFSG.KC.OpsV4

variable {V : Type}

@[expose] noncomputable def conj7G (O : Ops Nat V) (pw : Nat → Nat → Nat) (A T i : Nat) : Nat :=
  O.mul (O.mul (pw T i) A) (pw T (7 - i))

@[expose] noncomputable def frobG (O : Ops Nat V) (pw : Nat → Nat → Nat) (t A T : Nat) : Bool :=
  forceB (conj7G O pw A T 1) fun A₁ =>
    O.eq (O.mul A A) O.one && O.eq (pw T 7) O.one && O.commOK A A₁ &&
      O.commOK A (conj7G O pw A T 2) && O.eq (conj7G O pw A T 3) (O.mul A₁ A) &&
      O.vne (O.vmul (O.unit t) A) (O.unit t)

@[expose] noncomputable def frobL (c : Lay) (A B : Nat) (D : FrobData) : Bool :=
  progOK D.nregs D.prog && decide (D.ra < D.nregs) && decide (D.rt < D.nregs) &&
    decide (D.test < c.d) &&
    runC c D.prog (initR c A B D.nregs) fun R =>
      frobG (opsL c) (powK c) D.test (getR c R D.ra) (getR c R D.rt)

end CFSG.KC.OpsFrob

end
