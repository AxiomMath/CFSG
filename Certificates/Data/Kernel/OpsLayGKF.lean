module

public import Certificates.Data.Kernel.OpsV4
public import CFSG.GH74.Generic.GKFFusion
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public section

namespace CFSG.KC.OpsLayGKF

open CFSG.SectionRank.Native CFSG.GH74.Generic.Fusion CFSG.GH74.KGroups.J3 CFSG.KC.LQT
  CFSG.KC.OpsLayK CFSG.KC.OpsV4

variable {V : Type}

@[expose] noncomputable def fusTestG (O : Ops Nat V) (pw : Nat → Nat → Nat) (x0 y s n1 n2 : Nat) :
    Bool :=
  O.eq (O.mul s s) O.one && decide (n1 % 2 = 1) && decide (n2 % 2 = 1) &&
    O.eq (pw (O.mul s x0) n1) O.one && O.eq (pw (O.mul s y) n2) O.one

@[expose] noncomputable def gkfG (O : Ops Nat V) (pw : Nat → Nat → Nat) (D : FusData)
    (g : Nat → Nat) : Bool :=
  [g D.o0, g D.o1, g D.o2, g D.o3].all (fun X => O.eq (O.mul X X) O.one) &&
    O.commsOK [g D.o0, g D.o1, g D.o2, g D.o3] &&
    O.kerModOK O.one [g D.o0, g D.o1, g D.o2, g D.o3] D.tests &&
    (List.range 15).all fun k =>
      decide (D.sregs.getD k 0 < D.nregs) &&
        fusTestG O pw (g D.o0) (prodBase2 O [g D.o0, g D.o1, g D.o2, g D.o3] (k + 1))
          (g (D.sregs.getD k 0)) (D.n1s.getD k 0) (D.n2s.getD k 0)

@[expose] noncomputable def gkfFusK (c : Lay) (A B : Nat) (D : FusData) : Bool :=
  progOK D.nregs D.prog && [D.o0, D.o1, D.o2, D.o3].all (decide <| · < D.nregs) &&
    D.tests.all (decide <| · < c.d) &&
    (List.range 15).all (fun k => decide (D.n1s.getD k 0 < 65536) &&
      decide (D.n2s.getD k 0 < 65536)) &&
    runC c D.prog (initR c A B D.nregs) fun R => gkfG (opsL c) (powK c) D (getR c R)

end CFSG.KC.OpsLayGKF

end
