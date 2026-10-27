module

public import CFSG.Yardstones.M50b1bb4a7c08.Definitions
public import CFSG.Yardstones.M0ff270807621.Goals

public section

namespace CFSG.Yardstones.M50b1bb4a7c08

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3

theorem pfTablesRest :
    PhilipHall.Frame.Twin1711.PfTablesRest :=
  ⟨PhilipHall.Frame.Twin1711.TtK.sp1_proved, PhilipHall.Frame.Twin1711.Om1.om1_proved,
    PhilipHall.Frame.Twin1711.Om2.om2_proved, PhilipHall.Frame.Twin1711.Om2.om2p_proved⟩

theorem model1524Twin3Om :
    TL4.Model1524Twin3Om :=
  CFSG.ClassicalInvolution.Q3.TL4.E3S3O.model1524Twin3Om_proved

theorem thmCLeafE8E64 : ThmCLeafE8E64 :=
  TC.Thin.cLeafE8E64_proved (TC.Thin.PackIH 3)

theorem thmCLeafE29 : ThmCLeafE29 :=
  TC.Thin.cLeafE29_of_G (TC.Thin.cLeafE29G_proved (TC.Thin.PackIH 3))

theorem thmCLeafAE : ThmCLeafAE :=
  TC.Thin.cLeafAE_holds _

theorem thmDLeafE4Star :
    ThmDLeafE4Star :=
  ⟨Sec13.dLeafE4_three _, Sec13.dLeafStar_three _⟩

theorem thmDLeafEnd :
    ThmDLeafEnd :=
  Sec13.dLeafEnd_three _

theorem frameAEmptyP :
    PhilipHall.Frame.FrameAEmptyPf.FrameAEmptyP :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.frameAEmptyP_proved

theorem twinThinAll :
    TwinThinAll :=
  PhilipHall.Frame.twinThinAll_proved

theorem twinDiscPerpAll :
    TwinDiscPerpAll :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.twinDiscPerpSPAll_proved

theorem twinPerpBaseV3S23 :
    TwinPerpBaseV3S23 := fun n hA hP =>
  ⟨CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.twinPerpSmallE_proved n, CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.twinPerpV3E_proved n hA hP,
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.twinPerp233E_proved hA hP⟩

theorem twinPerpS24S25 :
    TwinPerpS24S25 := fun n hA hP =>
  ⟨CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.twinPerp24S_of_h3
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.EIHAll.of_eih (And.intro hA hP))
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW.t4Supply_of_twoClass n hA hP)
      CFSG.ClassicalInvolution.Q8P.Asc77.S24B.h3_unconditional,
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.twinPerp25A_of_typing_leaves
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.EIHAll.of_eih (And.intro hA hP))
      CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X.p25_a4_proved
      CFSG.ClassicalInvolution.Q8P.Asc77.P25R.ae5SqModel_of_cert
      CFSG.ClassicalInvolution.Q8P.Asc77.P25T.p25_typedO2_proved
      CFSG.ClassicalInvolution.Q8P.Asc77.P25T.p25_typedE4_proved
      CFSG.ClassicalInvolution.Q8P.Asc77.P25R.p25_ae5Excl_proved
      CFSG.ClassicalInvolution.Q8P.Asc77.P25R.p25_endL_proved⟩

theorem linkZ2L2Cases :
    LinkZ2L2Cases :=
  ⟨fun n => CFSG.ClassicalInvolution.Q3.TL4.Z2W.tightLinkZ2L2OuterR_plus n,
    fun n => CFSG.ClassicalInvolution.Q3.TL4.Z2W.tightLinkZ2L2InnerR_plus n⟩

theorem linkEdgeRigidAll :
    LinkEdgeRigidAll :=
  fun n => CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b.tightLinkEdgeRigidR_plus n

theorem tightR4OfGH74 :
    TightR4OfGH74 :=
  fun hGH h3 => CFSG.CGT.PushingUpLit.SolKNA.R4.tightR4_of_gh74 hGH h3
    (CFSG.Yardstones.M0ff270807621.r4EdgeFalse_holds hGH)

end CFSG.Yardstones.M50b1bb4a7c08
