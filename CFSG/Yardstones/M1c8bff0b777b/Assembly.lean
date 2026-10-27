module

public import CFSG.Yardstones.M1c8bff0b777b.Definitions
public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWired40
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf4Sp0Fin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Sp1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf2Om0Gen

public section

namespace CFSG.Yardstones.M1c8bff0b777b

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ComponentClassification.QuaternionComponent

theorem pfTables_of_tables1711Om (h : Tables1711Om) : PhilipHall.Frame.Twin1711.PfTables :=
  { sp0 := PhilipHall.Frame.Twin1711.Sp0K.sp0_proved
    sp1 := PhilipHall.Frame.Twin1711.TtK.sp1_proved
    om0 := PhilipHall.Frame.Twin1711.Om0.om0_proved
    om1 := h.1
    om2 := h.2.1
    om2p := h.2.2 }

theorem wiredInputs₄₀_of_yardstones (hGH : GH74SectionalModels) (h01 : CLeaf126R3)
    (h02 : CLeafAER3) (h03 : DLeafE4R3) (h04 : DLeafStarR3) (h05 : DLeafEndR3)
    (h06 : PhilipHall.Frame.FrameAEmptyPf.FrameCaseITG)
    (h07 : PhilipHall.Frame.FrameAEmptyPf.FrameCaseIITG) (h08 : TwinThinAll) (h09 : Tables1711Om)
    (h10 : TwinDiscPerpAll) (h11 : TwinPerpAll) (h12 : TL4.Model1524Twin3Om)
    (h13 : LinkZ2L2OuterAll) (h14 : LinkZ2L2InnerAll) (h15 : LinkEdgeRigidAll)
    (h16 : Thm3RStepGAll) :
    WiredInputs₄₀ where
  gh74 := hGH
  frameAEmptyP := PhilipHall.Frame.FrameAEmptyPf.frameAEmptyP_of_casesTG h16 h06 h07
  cLeafE8 := h01.1
  cLeafE64 := h01.2.1
  cLeafE29 := h01.2.2
  cLeafAE := h02
  dLeafE4 := h03
  dLeafStar := h04
  dLeafEnd := h05
  twinThin := h08
  pfTables := pfTables_of_tables1711Om h09
  twinDiscPerpSP := h10
  twinPerpSE := h11
  model1524Om := h12
  linkZ2L2Outer := h13
  linkZ2L2Inner := h14
  linkEdgeOdd := h15

section Route


theorem frontier_of_yardstones
    (hGH : GH74SectionalModels)
    (h01 : CLeaf126R3) (h02 : CLeafAER3) (h03 : DLeafE4R3) (h04 : DLeafStarR3)
    (h05 : DLeafEndR3) (h06 : PhilipHall.Frame.FrameAEmptyPf.FrameCaseITG)
    (h07 : PhilipHall.Frame.FrameAEmptyPf.FrameCaseIITG) (h08 : TwinThinAll) (h09 : Tables1711Om)
    (h10 : TwinDiscPerpAll) (h11 : TwinPerpAll) (h12 : TL4.Model1524Twin3Om)
    (h13 : LinkZ2L2OuterAll) (h14 : LinkZ2L2InnerAll) (h15 : LinkEdgeRigidAll)
    (h16 : Thm3RStepGAll)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (_hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({z} : Set G)))
    (hzJ : z ∈ J) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    CFSG.Assembly.ComponentType.OddLieType G ∨
      Nonempty (G ≃* CFSG.Assembly.ComponentType.M11) :=
  milestone_of_wired₄₀
    (wiredInputs₄₀_of_yardstones hGH h01 h02 h03 h04 h05 h06 h07 h08 h09 h10 h11 h12 h13 h14 h15
      h16)
    G hnonab z hz J hJ hzJ S hS

end Route

end CFSG.Yardstones.M1c8bff0b777b
