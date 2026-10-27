module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Data.Kernel.OpsLayK
public import CFSG.RankThree.Native.FiveTwoCert
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.KC.FiveTwoK

open CFSG.SectionRank.Native CFSG.RankThree.Native CFSG.KC.OpsK CFSG.KC.OpsMN CFSG.KC.LQT
  CFSG.KC.OpsLayK

variable {V : Type}

@[expose] noncomputable def movesN (O : Ops Nat V) (tests : List Nat) (X : Nat) : Bool :=
  tests.any fun k => O.vne (O.vmul (O.unit k) X) (O.unit k)

@[expose] noncomputable def orderN (O : Ops Nat V) (D : FiveTwoData) (R : List Nat) : Bool :=
  O.eq (powN O 11 (getN R D.w) 10) O.one &&
    movesN O D.base.tests (powN O 6 (getN R D.w) 5) &&
    movesN O D.base.tests (powN O 3 (getN R D.w) 2)

@[expose] noncomputable def fiveN (O : Ops Nat V) (A B : Nat) (D : FiveTwoData) : Bool :=
  D.base.prog.all (Op.lt D.base.nregs) && decide (D.w < D.base.nregs) &&
    regsN O A B D.base.nregs D.base.prog (orderN O D)

@[expose] noncomputable def movesL (c : Lay) (tests : List Nat) (X : Nat) : Bool :=
  tests.any fun k => decide (k < c.d) && !Nat.beq (c.vec (c.unit k) X) (c.unit k)

@[expose] noncomputable def orderL (c : Lay) (D : FiveTwoData) (R : List Nat) : Bool :=
  Nat.beq (powK c (getR c R D.w) 10) c.ONE &&
    movesL c D.base.tests (powK c (getR c R D.w) 5) &&
    movesL c D.base.tests (powK c (getR c R D.w) 2)

@[expose] noncomputable def fiveL (c : Lay) (A B : Nat) (D : FiveTwoData) : Bool :=
  progOK D.base.nregs D.base.prog && decide (D.w < D.base.nregs) &&
    runC c D.base.prog (initR c A B D.base.nregs) (orderL c D)

end CFSG.KC.FiveTwoK

end
