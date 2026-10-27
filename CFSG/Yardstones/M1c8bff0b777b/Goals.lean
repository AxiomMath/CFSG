module

public import CFSG.Yardstones.M1c8bff0b777b.Definitions
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.Final
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G9
public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b10
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM3P
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSEProved

public section

namespace CFSG.Yardstones.M1c8bff0b777b

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3

section Certified


theorem cLeaf126R3_holds : CLeaf126R3 :=
  TC.Thin.cLeaf126_proved (TC.Thin.PackIH 3)

theorem cLeafAER3_holds : CLeafAER3 :=
  TC.Thin.cLeafAE_holds _

theorem dLeafE4R3_holds :
    DLeafE4R3 :=
  Sec13.dLeafE4_three _

theorem dLeafStarR3_holds : DLeafStarR3 :=
  Sec13.dLeafStar_three _

theorem dLeafEndR3_holds :
    DLeafEndR3 :=
  Sec13.dLeafEnd_three _

theorem frameCaseITG_holds :
    PhilipHall.Frame.FrameAEmptyPf.FrameCaseITG :=
  PhilipHall.Frame.FrameAEmptyPf.frameCaseITG_proved

theorem frameCaseIITG_holds :
    PhilipHall.Frame.FrameAEmptyPf.FrameCaseIITG :=
  PhilipHall.Frame.FrameAEmptyPf.frameCaseIITG_proved

theorem twinThinAll_holds :
    TwinThinAll :=
  PhilipHall.Frame.twinThinAll_proved

theorem twinDiscPerpAll_holds :
    TwinDiscPerpAll :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.twinDiscPerpSPAll_proved

theorem twinPerpAll_holds :
    TwinPerpAll := fun _ hA hP =>
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.twinCorePerpSE'_proved hA hP

theorem linkZ2L2OuterAll_holds :
    LinkZ2L2OuterAll :=
  fun n => CFSG.ClassicalInvolution.Q3.TL4.Z2W.tightLinkZ2L2OuterR_plus n

theorem linkZ2L2InnerAll_holds :
    LinkZ2L2InnerAll :=
  fun n => CFSG.ClassicalInvolution.Q3.TL4.Z2W.tightLinkZ2L2InnerR_plus n

theorem linkEdgeRigidAll_holds :
    LinkEdgeRigidAll :=
  fun n => CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b.tightLinkEdgeRigidR_plus n

theorem thm3RStepGAll_holds :
    Thm3RStepGAll :=
  PhilipHall.Thm3Step.thm3RStepGAll_proved

end Certified

theorem tables1711Om_holds :
    Tables1711Om :=
  ⟨PhilipHall.Frame.Twin1711.Om1.om1_proved, PhilipHall.Frame.Twin1711.Om2.om2_proved,
    PhilipHall.Frame.Twin1711.Om2.om2p_proved⟩

theorem model1524Twin3Om_holds :
    TL4.Model1524Twin3Om :=
  CFSG.ClassicalInvolution.Q3.TL4.E3S3O.model1524Twin3Om_proved

end CFSG.Yardstones.M1c8bff0b777b
