module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Data.Kernel.OpsLayK
public import CFSG.RankThree.PartTwo.Census.Sporadic.RankFourCert
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.KC.OpsW4N

open CFSG.SectionRank.Native CFSG.KC.OpsK CFSG.KC.OpsMN CFSG.KC.LQT CFSG.KC.OpsLayK

variable {V : Type}

@[expose] noncomputable def w4OK (O : Ops Nat V) (tests : List Nat) (xs : List Nat) (T : Nat) :
    Bool :=
  O.elemOK xs tests && O.eq (O.mul T T) O.one &&
    tests.any (fun k => O.vne (O.vmul (O.unit k) T) (O.unit k)) && xs.all (fun X => O.commOK X T)

@[expose] noncomputable def w4N (O : Ops Nat V) (A B : Nat) (D : Data) (inv : Nat) : Bool :=
  decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && D.outs.all (decide <| · < D.nregs) &&
    decide (inv < D.nregs) &&
    regsN O A B D.nregs D.prog fun R =>
      forceL (D.outs.map (getN R)) fun xs => forceB (getN R inv) fun T => w4OK O D.tests xs T

@[expose] noncomputable def w4L (c : Lay) (A B : Nat) (D : Data) (inv : Nat) : Bool :=
  progOK D.nregs D.prog && D.outs.all (decide <| · < D.nregs) && decide (inv < D.nregs) &&
    D.tests.all (decide <| · < c.d) &&
  runC c D.prog (initR c A B D.nregs) fun R =>
    let T := getR c R inv
    let xs := D.outs.map (getR c R)
    elemK c xs D.tests && Nat.beq (c.mul T T) c.ONE &&
      D.tests.any (fun k => !Nat.beq (c.vec (c.unit k) T) (c.unit k)) &&
      xs.all (fun X => commK c X T)

end CFSG.KC.OpsW4N

end
