module

public import CFSG.ClassicalInvolution.Q3.TL3T27
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711E4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetWire
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfMain
public import CFSG.ClassicalInvolution.Q3.TL4StepDefs
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2DefsB
public import CFSG.ClassicalInvolution.Q3.TL4LinkDiscC

public section

namespace CFSG.Yardstones.M50b1bb4a7c08

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3

@[expose] def ThmCLeafE8E64 : Prop :=
  TC.Thin.CLeafE8 3 (TC.Thin.PackIH 3) ∧ TC.Thin.CLeafE64 3 (TC.Thin.PackIH 3)

@[expose] def ThmCLeafE29 : Prop :=
  TC.Thin.CLeafE29 3 (TC.Thin.PackIH 3)

@[expose] def ThmCLeafAE : Prop :=
  TC.Thin.CLeafAE 3 (TC.Thin.PackIH 3)

@[expose] def ThmDLeafE4Star : Prop :=
  TC.Thin.DLeafE4 3 (TC.Thin.PackIH 3) ∧ TC.Thin.DLeafStar 3 (TC.Thin.PackIH 3)

@[expose] def ThmDLeafEnd : Prop :=
  TC.Thin.DLeafEnd 3 (TC.Thin.PackIH 3)

@[expose] def TwinThinAll : Prop :=
  ∀ n : ℕ, CIT3Below n → TL4.TightBelowRPlus 3 n → PhilipHall.Frame.TwinThinInput n

@[expose] def TwinDiscPerpAll : Prop :=
  ∀ n : ℕ, PhilipHall.Frame.TwinCoreDiscPerpSP n

@[expose] def TwinPerpBaseV3S23 : Prop :=
  ∀ n : ℕ, CIT3Below n → TL4.TightBelowRPlus 3 n →
    PhilipHall.Frame.TwinPerp.TwinPerpSmallE n ∧ PhilipHall.Frame.TwinPerp.TwinPerpV3E n ∧
      PhilipHall.Frame.TwinPerp.TwinPerp233E n

@[expose] def TwinPerpS24S25 : Prop :=
  ∀ n : ℕ, CIT3Below n → TL4.TightBelowRPlus 3 n →
    PhilipHall.Frame.TwinPerp.TwinPerp24S n ∧ PhilipHall.Frame.TwinPerp.TwinPerp25A n

@[expose] def LinkZ2L2Cases : Prop :=
  (∀ n : ℕ, TL4.PlusLeaf TL4.TightLinkZ2L2OuterR n) ∧
    ∀ n : ℕ, TL4.PlusLeaf TL4.TightLinkZ2L2InnerR n

@[expose] def LinkEdgeRigidAll : Prop :=
  ∀ n : ℕ, TL4.PlusLeaf TL4.LinkDisc.TightLinkEdgeRigidR n

@[expose] def TightR4OfGH74 : Prop :=
  GH74SectionalModels → (∀ n : ℕ, CIT3Below n → TL4.TightBelowRPlus 3 n) → TightR4

end CFSG.Yardstones.M50b1bb4a7c08
