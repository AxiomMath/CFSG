module

public import CFSG.Yardstones.M0ff270807621.Definitions
public import CFSG.RankThree.PartOne.S12.PartOneCIT
public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentWired40
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TightR4Assembly
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf21All
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711PfRest
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5Sp1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.Main

public section

namespace CFSG.Yardstones.M0ff270807621

section Cit3

theorem wiredInputs₄₀_of_yardstones
    (hGH : CFSG.ClassicalInvolution.GH74SectionalModels)
    (h06 : CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.FrameAEmptyP)
    (h07 : ThmCThinE8E64E29) (h08 : ThmCAE) (h09 : ThmD2Leaves) (h10 : TwinConnCoreInputs)
    (h11 : TwinDiscPerpSPAll) (h12 : TwinPerpSEAll)
    (h13 : CFSG.ClassicalInvolution.Q3.TL4.Model1524Twin3Om) (h14 : LinkZ2L2Leaves)
    (h15 : LinkEdgeRigidAll) :
    CFSG.ComponentClassification.QuaternionComponent.WiredInputs₄₀ := by
  obtain ⟨hE8, hE64, hE29⟩ := h07
  obtain ⟨hD4, hDS, hDE⟩ := h09
  obtain ⟨hThin, hTab⟩ := h10
  obtain ⟨hOut, hIn⟩ := h14
  exact
    { gh74 := hGH
      frameAEmptyP := h06
      cLeafE8 := hE8
      cLeafE64 := hE64
      cLeafE29 := hE29
      cLeafAE := h08
      dLeafE4 := hD4
      dLeafStar := hDS
      dLeafEnd := hDE
      twinThin := fun n _ _ => hThin n
      pfTables := hTab
      twinDiscPerpSP := h11
      twinPerpSE := h12
      model1524Om := h13
      linkZ2L2Outer := hOut
      linkZ2L2Inner := hIn
      linkEdgeOdd := h15 }

section Count

theorem tightLargeEdgeSR_of_countPM
    (h : R4CountPM) (r : ℕ) (hr : 4 ≤ r) (n : ℕ) :
    CFSG.CGT.PushingUpLit.SolKNA.R4.TightLargeEdgeSR r n :=
  CFSG.CGT.PushingUpLit.SolKNA.R4.tightLargeEdgeSR_of_thm6SylowBelowSRc
    (CFSG.CGT.PushingUpLit.SolKNA.R4.tightThm6SylowBelowSRc_of_parts
      CFSG.ClassicalInvolution.Disconnected.AschTight.goldschmidtB3Tmp_holds
      (CFSG.CGT.PushingUpLit.SolKNA.R4.sylowPartsR_holds r)
      (CFSG.CGT.PushingUpLit.SolKNA.R4.tightC19_11bSR_of_F1
        (CFSG.CGT.PushingUpLit.SolKNA.R4.tightF1SR_holds hr))
      (CFSG.CGT.PushingUpLit.SolKNA.R4.tightCountRc_of_pm hr (h r)))
    n (fun hA hb => ⟨hA, hb⟩)

section TightR4Part

theorem tightR4_of_yardstones
    (hGH : CFSG.ClassicalInvolution.GH74SectionalModels)
    (h3 : ∀ n, CFSG.ClassicalInvolution.Q3.CIT3Below n →
      CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n)
    (h01 : R4CountPM) (h02 : R4EdgeFalse)
    (h03 : R4CentTwin) (h04 : R4TwistAllTwin) (h05 : R4SmallLeaves) :
    CFSG.ClassicalInvolution.Q3.TightR4 :=
  CFSG.CGT.PushingUpLit.SolKNA.R4.tightR4_of_lowerClass h3 (h04 hGH)
    (fun r hr => by
      obtain ⟨hM11, hM12, hL33, hU33, hG23, hD43, hL53, hP43, hT⟩ := h05 r hr
      exact CFSG.CGT.PushingUpLit.SolKNA.R4.tightSmallBaseR_of_parts r hGH hM11 hM12 hL33 hU33 hG23
        hD43 hL53 hP43 (hT hGH))
    (fun r hr => tightLargeEdgeSR_of_countPM h01 r hr) (h02 hGH) (h03 hGH)

section Main

theorem part_one_outcome_of_yardstones
    (h01 : R4CountPM) (h02 : R4EdgeFalse) (h03 : R4CentTwin) (h04 : R4TwistAllTwin)
    (h05 : R4SmallLeaves)
    (h06 : CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.FrameAEmptyP)
    (h07 : ThmCThinE8E64E29) (h08 : ThmCAE) (h09 : ThmD2Leaves) (h10 : TwinConnCoreInputs)
    (h11 : TwinDiscPerpSPAll) (h12 : TwinPerpSEAll)
    (h13 : CFSG.ClassicalInvolution.Q3.TL4.Model1524Twin3Om) (h14 : LinkZ2L2Leaves)
    (h15 : LinkEdgeRigidAll)
    (hGH : CFSG.ClassicalInvolution.GH74SectionalModels)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) (hchar : CFSG.Assembly.IsCharTwoType G)
    (he : CFSG.Assembly.evenRank G = 3)
    (hq : ∃ q : ℕ, q.Prime ∧ 3 < q ∧ CFSG.Assembly.RankThreeEven.localRank q G = 3) :
    CFSG.Assembly.RankThreeEven.IModel G ∨ CFSG.Assembly.RankThreeEven.AschCoreLocal G 2 := by
  have h40 := wiredInputs₄₀_of_yardstones hGH h06 h07 h08 h09 h10 h11 h12 h13 h14 h15
  have gp : CFSG.ComponentClassification.QuaternionComponent.CITPowBelow3 :=
    CFSG.ComponentClassification.QuaternionComponent.citPowBelow3_of_gh74_memberFreeP h40.gh74
      fun gp => CFSG.ComponentClassification.QuaternionComponent.memberFreeSocle_of_wired₄₀ h40 gp
  exact CFSG.RankThree.PartOne.part_one_outcome_of_qcw19 ((h40.toWired₂₀ gp).toWired₁₉)
    (fun _ => tightR4_of_yardstones hGH
      (fun n hA => CFSG.ClassicalInvolution.Q3.TL4.tightBelowRPlus_of_step (h40.steps gp) n hA)
      h01 h02 h03 h04 h05) G hnonab hK hchar he hq

section TwinConn


theorem twinConnCoreInputs_of_yardstones
    (h01 : R4CountPM) (h02 : R4EdgeFalse) (h03 : R4CentTwin) (h04 : R4TwistAllTwin)
    (h05 : R4SmallLeaves)
    (h06 : CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.FrameAEmptyP)
    (h07 : ThmCThinE8E64E29) (h08 : ThmCAE) (h09 : ThmD2Leaves)
    (h11 : TwinDiscPerpSPAll) (h12 : TwinPerpSEAll)
    (h13 : CFSG.ClassicalInvolution.Q3.TL4.Model1524Twin3Om) (h14 : LinkZ2L2Leaves)
    (h15 : LinkEdgeRigidAll)
    (hGH : CFSG.ClassicalInvolution.GH74SectionalModels) : TwinConnCoreInputs := by
  let h40 : CFSG.ComponentClassification.QuaternionComponent.WiredInputs₄₀ :=
    { gh74 := hGH
      frameAEmptyP := h06
      cLeafE8 := h07.1
      cLeafE64 := h07.2.1
      cLeafE29 := h07.2.2
      cLeafAE := h08
      dLeafE4 := h09.1
      dLeafStar := h09.2.1
      dLeafEnd := h09.2.2
      twinThin := CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.twinThinAll_proved
      pfTables := CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.pfTables_of_rest
        ⟨CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK.sp1_proved,
         CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1.om1_proved,
         CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2.om2_proved,
         CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2.om2p_proved⟩
      twinDiscPerpSP := h11
      twinPerpSE := h12
      model1524Om := h13
      linkZ2L2Outer := h14.1
      linkZ2L2Inner := h14.2
      linkEdgeOdd := h15 }
  have gp : CFSG.ComponentClassification.QuaternionComponent.CITPowBelow3 :=
    CFSG.ComponentClassification.QuaternionComponent.citPowBelow3_of_gh74_memberFreeP h40.gh74
      fun gp => CFSG.ComponentClassification.QuaternionComponent.memberFreeSocle_of_wired₄₀ h40 gp
  have hpkg : ∀ n, CFSG.ClassicalInvolution.Q3.CIT3Below n →
      CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n :=
    CFSG.ClassicalInvolution.Q3.TL4.tightBelowRPlus_of_step (h40.steps gp)
  have hC : CFSG.ClassicalInvolution.Q3.CIT3Inductive :=
    CFSG.CGT.PushingUpLit.SolKNA.cit3Inductive_of_citInputs
      (CFSG.CGT.PushingUpLit.SolKNA.citInputs_of_qcw19 ((h40.toWired₂₀ gp).toWired₁₉)
        fun hG => tightR4_of_yardstones hG hpkg h01 h02 h03 h04 h05)
  have hB : ∀ n, CFSG.ClassicalInvolution.Q3.CIT3Below n :=
    fun n Y _ _ _ Λ hΛ => hC Y Λ hΛ
  exact ⟨fun n => CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.twinThinAll_proved n
    (hB n) (hpkg n (hB n)), h40.pfTables⟩

end TwinConn

end Main

end TightR4Part

end Count

end Cit3

end CFSG.Yardstones.M0ff270807621
