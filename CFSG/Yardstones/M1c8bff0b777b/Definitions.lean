module

public import CFSG.ClassicalInvolution.Q3.TL3T27
public import CFSG.ClassicalInvolution.Q3.TL4StepDefs
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2DefsB
public import CFSG.ClassicalInvolution.Q3.TL4LinkDiscC
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf49G3At
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711E4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711PfTables
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetWire

public section

namespace CFSG.Yardstones.M1c8bff0b777b

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3

section Props

@[expose] def CLeaf126R3 : Prop :=
  TC.Thin.CLeafE8 3 (TC.Thin.PackIH 3) ∧ TC.Thin.CLeafE64 3 (TC.Thin.PackIH 3) ∧
    TC.Thin.CLeafE29 3 (TC.Thin.PackIH 3)

@[expose] def CLeafAER3 : Prop := TC.Thin.CLeafAE 3 (TC.Thin.PackIH 3)

@[expose] def DLeafE4R3 : Prop := TC.Thin.DLeafE4 3 (TC.Thin.PackIH 3)

@[expose] def DLeafStarR3 : Prop := TC.Thin.DLeafStar 3 (TC.Thin.PackIH 3)

@[expose] def DLeafEndR3 : Prop := TC.Thin.DLeafEnd 3 (TC.Thin.PackIH 3)

@[expose] def TwinThinAll : Prop :=
  ∀ n : ℕ, CIT3Below n → TL4.TightBelowRPlus 3 n → PhilipHall.Frame.TwinThinInput n

@[expose] def Tables1711Om : Prop :=
  PhilipHall.Frame.Twin1711.NoSandwichAt PhilipHall.Frame.Twin1711.ModOm1 ∧
    PhilipHall.Frame.Twin1711.SandwichSizeTwoAt PhilipHall.Frame.Twin1711.ModOm2 ∧
    PhilipHall.Frame.Twin1711.PairingAt PhilipHall.Frame.Twin1711.ModOm2

@[expose] def TwinDiscPerpAll : Prop := ∀ n : ℕ, PhilipHall.Frame.TwinCoreDiscPerpSP n

@[expose] def TwinPerpAll : Prop :=
  ∀ n : ℕ, CIT3Below n → TL4.TightBelowRPlus 3 n → PhilipHall.Frame.TwinCorePerpSE' n

@[expose] def LinkZ2L2OuterAll : Prop := ∀ n : ℕ, TL4.PlusLeaf TL4.TightLinkZ2L2OuterR n

@[expose] def LinkZ2L2InnerAll : Prop := ∀ n : ℕ, TL4.PlusLeaf TL4.TightLinkZ2L2InnerR n

@[expose] def LinkEdgeRigidAll : Prop := ∀ n : ℕ, TL4.PlusLeaf TL4.LinkDisc.TightLinkEdgeRigidR n

end Props

section Theorem3

@[expose] def Thm3RStepGAll : Prop :=
  ∀ m : ℕ, PhilipHall.Frame.FrameAEmptyPf.Thm3A.Thm3RStepG m

end Theorem3

end CFSG.Yardstones.M1c8bff0b777b
