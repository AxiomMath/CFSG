module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Step
public import CFSG.CGT.PushingUpLit.SolKNA.R4.Count
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LowerClass
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711E4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711PfTables
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetWire
public import CFSG.ClassicalInvolution.Q3.TL3T27
public import CFSG.ClassicalInvolution.Q3.TL4LinkDiscC
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2DefsB
public import CFSG.ClassicalInvolution.Q3.TL4StepDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.Yardstones.M0ff270807621

@[expose] def R4CountPM : Prop :=
  ∀ r : ℕ, CFSG.CGT.PushingUpLit.SolKNA.R4.TightPMR r
    (fun n => CFSG.ClassicalInvolution.Q3.CIT3Below n ∧ CFSG.ClassicalInvolution.Q3.TightBelowR r n)

@[expose] def R4EdgeFalse : Prop :=
  CFSG.ClassicalInvolution.GH74SectionalModels →
    ∀ r : ℕ, 4 ≤ r → ∀ n : ℕ, CFSG.CGT.PushingUpLit.SolKNA.R4.LowerClassR r n →
      CFSG.CGT.PushingUpLit.SolKNA.R4.TightEdgeFalseSR r n

@[expose] def R4CentTwin : Prop :=
  CFSG.ClassicalInvolution.GH74SectionalModels →
    ∀ r : ℕ, 4 ≤ r → ∀ n : ℕ, CFSG.CGT.PushingUpLit.SolKNA.R4.LowerClassR r n →
      CFSG.CGT.PushingUpLit.SolKNA.R4.TightCentTwinLiftR r n

@[expose] def R4TwistAllTwin : Prop :=
  CFSG.ClassicalInvolution.GH74SectionalModels →
    ∀ r : ℕ, 4 ≤ r → ∀ n : ℕ, CFSG.CGT.PushingUpLit.SolKNA.R4.LowerClassR r n →
      CFSG.CGT.PushingUpLit.SolKNA.R4.TightTwistAllTwinR r n

@[expose] def R4SmallLeaves : Prop :=
  ∀ r : ℕ, 4 ≤ r →
    CFSG.CGT.PushingUpLit.SolKNA.R4.SmallLeafR r CFSG.ClassicalInvolution.Q3.TA3.SmallM11 ∧
    CFSG.CGT.PushingUpLit.SolKNA.R4.SmallLeafR r CFSG.ClassicalInvolution.Q3.TA3.SmallM12 ∧
    CFSG.CGT.PushingUpLit.SolKNA.R4.SmallLeafR r
      (fun F _ => CFSG.Blueprint.LieModel F .PSL 3 3 1) ∧
    CFSG.CGT.PushingUpLit.SolKNA.R4.SmallLeafR r
      (fun F _ => CFSG.Blueprint.LieModel F .PSU 3 3 1) ∧
    CFSG.CGT.PushingUpLit.SolKNA.R4.SmallLeafR r
      (fun F _ => CFSG.Blueprint.LieModel F .G2 0 3 1) ∧
    CFSG.CGT.PushingUpLit.SolKNA.R4.SmallLeafR r
      (fun F _ => CFSG.Blueprint.LieModel F .trialityD4 0 3 1) ∧
    CFSG.CGT.PushingUpLit.SolKNA.R4.SmallLeafR r
      (fun F _ => CFSG.Blueprint.LieModel F .PSL 5 3 1) ∧
    CFSG.CGT.PushingUpLit.SolKNA.R4.SmallLeafR r
      (fun F _ => CFSG.Blueprint.LieModel F .PSp 2 3 1) ∧
    (CFSG.ClassicalInvolution.GH74SectionalModels →
      CFSG.CGT.PushingUpLit.SolKNA.R4.NoCentralTwinR r)

@[expose] def ThmCThinE8E64E29 : Prop :=
  CFSG.ClassicalInvolution.Q3.TC.Thin.CLeafE8 3 (CFSG.ClassicalInvolution.Q3.TC.Thin.PackIH 3) ∧
    CFSG.ClassicalInvolution.Q3.TC.Thin.CLeafE64 3
      (CFSG.ClassicalInvolution.Q3.TC.Thin.PackIH 3) ∧
    CFSG.ClassicalInvolution.Q3.TC.Thin.CLeafE29 3 (CFSG.ClassicalInvolution.Q3.TC.Thin.PackIH 3)

@[expose] def ThmCAE : Prop :=
  CFSG.ClassicalInvolution.Q3.TC.Thin.CLeafAE 3 (CFSG.ClassicalInvolution.Q3.TC.Thin.PackIH 3)

@[expose] def ThmD2Leaves : Prop :=
  CFSG.ClassicalInvolution.Q3.TC.Thin.DLeafE4 3 (CFSG.ClassicalInvolution.Q3.TC.Thin.PackIH 3) ∧
    CFSG.ClassicalInvolution.Q3.TC.Thin.DLeafStar 3
      (CFSG.ClassicalInvolution.Q3.TC.Thin.PackIH 3) ∧
    CFSG.ClassicalInvolution.Q3.TC.Thin.DLeafEnd 3 (CFSG.ClassicalInvolution.Q3.TC.Thin.PackIH 3)

@[expose] def TwinConnCoreInputs : Prop :=
  (∀ n : ℕ, CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinInput n) ∧
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.PfTables

@[expose] def TwinDiscPerpSPAll : Prop :=
  ∀ n : ℕ, CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCoreDiscPerpSP n

@[expose] def TwinPerpSEAll : Prop :=
  ∀ n : ℕ, CFSG.ClassicalInvolution.Q3.CIT3Below n →
    CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n →
      CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCorePerpSE' n

@[expose] def LinkZ2L2Leaves : Prop :=
  (∀ n : ℕ, CFSG.ClassicalInvolution.Q3.TL4.PlusLeaf
      CFSG.ClassicalInvolution.Q3.TL4.TightLinkZ2L2OuterR n) ∧
    ∀ n : ℕ, CFSG.ClassicalInvolution.Q3.TL4.PlusLeaf
      CFSG.ClassicalInvolution.Q3.TL4.TightLinkZ2L2InnerR n

@[expose] def LinkEdgeRigidAll : Prop :=
  ∀ n : ℕ, CFSG.ClassicalInvolution.Q3.TL4.PlusLeaf
    CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.TightLinkEdgeRigidR n

end CFSG.Yardstones.M0ff270807621
