module

public import CFSG.Yardstones.M0ff270807621.Assembly
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.Final
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G9
public import CFSG.CGT.PushingUpLit.SolKNA.R4.EdgeFalseLowerClass
public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b10
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM3P
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSEProved

public section

namespace CFSG.Yardstones.M0ff270807621

theorem r4SmallLeaves_holds :
    R4SmallLeaves := fun _ hr => CFSG.CGT.PushingUpLit.SolKNA.R4.r4SmallLeaves_cond hr

theorem model1524Twin3Om_holds :
    CFSG.ClassicalInvolution.Q3.TL4.Model1524Twin3Om :=
  CFSG.ClassicalInvolution.Q3.TL4.E3S3O.model1524Twin3Om_proved

section Cit3

theorem r4CountPM_holds : R4CountPM :=
  fun r => CFSG.CGT.PushingUpLit.SolKNA.R4.tightPMR r _

theorem r4EdgeFalse_holds :
    R4EdgeFalse :=
  fun hGH _ hr _ hL => CFSG.CGT.PushingUpLit.SolKNA.R4.tightEdgeFalseSR_of_lowerClass hGH hr hL

theorem r4CentTwin_holds :
    R4CentTwin :=
  fun hGH => CFSG.CGT.PushingUpLit.SolKNA.R4.r4CentTwin_of_mainInputs hGH
    CFSG.CGT.PushingUpLit.SolKNA.R4.twinMainInputsR_holds

theorem r4TwistAllTwin_holds :
    R4TwistAllTwin :=
  fun hGH => CFSG.CGT.PushingUpLit.SolKNA.R4.r4TwistAllTwin_of_mainInputs hGH
    CFSG.CGT.PushingUpLit.SolKNA.R4.twinMainInputsR_holds

theorem frameAEmptyP_holds :
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.FrameAEmptyP :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.frameAEmptyP_proved

theorem thmCThinE8E64E29_holds : ThmCThinE8E64E29 :=
  CFSG.ClassicalInvolution.Q3.TC.Thin.cLeaf126_proved (CFSG.ClassicalInvolution.Q3.TC.Thin.PackIH 3)

theorem thmCAE_holds : ThmCAE :=
  CFSG.ClassicalInvolution.Q3.TC.Thin.cLeafAE_holds _

theorem thmD2Leaves_holds :
    ThmD2Leaves :=
  ⟨CFSG.ClassicalInvolution.Q3.Sec13.dLeafE4_three _,
    CFSG.ClassicalInvolution.Q3.Sec13.dLeafStar_three _,
    CFSG.ClassicalInvolution.Q3.Sec13.dLeafEnd_three _⟩


theorem twinDiscPerpSPAll_holds :
    TwinDiscPerpSPAll :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.twinDiscPerpSPAll_proved

theorem twinPerpSEAll_holds :
    TwinPerpSEAll := fun _ hA hP =>
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.twinCorePerpSE'_proved hA hP

theorem linkZ2L2Leaves_holds :
    LinkZ2L2Leaves :=
  ⟨fun n => CFSG.ClassicalInvolution.Q3.TL4.Z2W.tightLinkZ2L2OuterR_plus n,
    fun n => CFSG.ClassicalInvolution.Q3.TL4.Z2W.tightLinkZ2L2InnerR_plus n⟩

theorem linkEdgeRigidAll_holds :
    LinkEdgeRigidAll :=
  fun n => CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b.tightLinkEdgeRigidR_plus n

theorem twinConnCoreInputs_holds :
    TwinConnCoreInputs :=
  twinConnCoreInputs_of_yardstones r4CountPM_holds r4EdgeFalse_holds r4CentTwin_holds
    r4TwistAllTwin_holds r4SmallLeaves_holds frameAEmptyP_holds thmCThinE8E64E29_holds
    thmCAE_holds thmD2Leaves_holds twinDiscPerpSPAll_holds twinPerpSEAll_holds
    model1524Twin3Om_holds linkZ2L2Leaves_holds linkEdgeRigidAll_holds
    CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models

end Cit3

end CFSG.Yardstones.M0ff270807621
