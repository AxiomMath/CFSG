module

public import CFSG.Yardstones.M0362f3a873a3.Definitions
public import CFSG.Yardstones.M0362f3a873a3.AltCyclic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Sec
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitBalance
public import CFSG.Milestones.CL_LIT_classical_involution_theorem
public import CFSG.Milestones.CL_LIT_GH74_sectional_two_rank_four
public import CFSG.Milestones.CTU_KProper_simple_unbalanced_recognition
public import CFSG.LocalAnalysis.OddStandard.OddLieHarris82Simple

public section

namespace CFSG.Yardstones.M0362f3a873a3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.OddStandard
open CFSG.OddStandard.AltStdSec CFSG.OddStandard.AltStdBal

theorem kProperSimpleUnbalancedUOutcome_of_milestone
    (hU : type_of% @CFSG.Milestones.ctu_kproper_simple_unbalanced_recognition) :
    KProperSimpleUnbalancedUOutcome := by
  intro G _ _ _ hnonab hK hz
  obtain ⟨z, hz2, hu⟩ := hz
  rcases hU G hnonab hK z hz2 hu with hlie | ⟨n, h7, h3, ⟨e⟩⟩
  · exact CFSG.ComponentClassification.GSThmB.Eight2.uOutcome_of_oddLieType hlie
  · exact CFSG.ComponentClassification.GrSLit.uOutcome_of_mulEquiv_alternating
      (Nat.odd_iff.2 (by omega)) h7 h3 e

theorem oddLieThm187bResidualMult_of_split (hF3 : SmallF3StandardOddLieU)
    (hL2 : OddLieThm187bResidualL2Ree) (hHigh : OddLieThm187bResidualHigherRank) :
    OddLieThm187bResidualMult := by
  intro G _ _ L hS hU hlie h5 h6 hhsf hcase S hcyc
  by_cases hsmall : SmallF3LieQuotient (L ⧸ center L)
  · have := hS.simple
    exact Or.inr (Or.inl (hF3 G hS.nonab hS.kProper hU L hS.standard hsmall))
  · by_cases hl2 : L2OrReeLieQuotient (L ⧸ center L)
    · exact hL2 G L hS hU hlie hl2 h5 h6 hhsf hcase S hcyc
    · exact hHigh G L hS hU hlie hsmall hl2 h5 h6 hhsf hcase S hcyc

theorem frontierModels_of_yardstones
    (y01 : AltStdBalancedOrder2InnerSmall) (y02 : ShapeTwoSmallNine)
    (y03 : ShapeTwoTenNoSwapPartnerNoCentralStdHS) (y04 : ShapeTwoTenSwapPartnerStdHS)
    (y05 : CFSG.EvenSporadicStandard.HSStd.HSSection5)
    (y06 : CFSG.EvenSporadicStandard.TwoHS.HaradaHNRecognitionKP)
    (y07 : CFSG.EvenSporadicStandard.TwoHS.GH312Fixed)
    (y08 : CFSG.ComponentClassification.HarrisLit.Harris82Theorem1SimpleKProperOdd)
    (y09 : SmallF3StandardOddLieU) (y10 : OddLieThm187bResidualL2Ree)
    (y11 : OddLieThm187bResidualHigherRank)
    (y12 : CFSG.ComponentClassification.GrSLit.HeldKSwapped)
    (hCIT : type_of% @CFSG.Milestones.cl_lit_classical_involution_theorem_models)
    (hGH : type_of% @CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models)
    (hU : type_of% @CFSG.Milestones.ctu_kproper_simple_unbalanced_recognition)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (htype : Blueprint.Recognition.Exact.OddStandardType (L ⧸ Subgroup.center L)) :
    (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨ Blueprint.OddLieType G ∨
      (Blueprint.NativeSporadic.IsSporadic G .M12 ∨ Blueprint.NativeSporadic.IsSporadic G .J1 ∨
        Blueprint.NativeSporadic.IsSporadic G .J2 ∨ Blueprint.NativeSporadic.IsSporadic G .HS ∨
        Blueprint.NativeSporadic.IsSporadic G .McL ∨ Blueprint.NativeSporadic.IsSporadic G .Ly ∨
        Blueprint.NativeSporadic.IsSporadic G .Suz ∨ Blueprint.NativeSporadic.IsSporadic G .He ∨
        Blueprint.NativeSporadic.IsSporadic G .ONan) := by
  have hHS : ShapeTwoTenStdHS :=
    shapeTwoTenStdHS_of_parts' CFSG.SeitzReduction.gls3OddLieAutComponentsInput
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput shapeTwoTenL44Excl_holds
      y03 y04
  have h7 : CFSG.EvenSporadicStandard.TwoHSGivesHN :=
    CFSG.EvenSporadicStandard.Frontier.child7_of_frontier y06 y07
  exact ct_odd_standard_recognition_frontier_models_of_shapeTwoTen y01
    (shapeTwoSmallTen_of_yardstones y02 hHS y05 h7) hCIT hGH
    (oddLieThm187b_of_harris82_of_mult_of_simpleKProperOdd y08
      (oddLieThm187bResidualMult_of_split y09 y10 y11))
    (kProperSimpleUnbalancedUOutcome_of_milestone hU) y12 G hnonab hK L hL htype

theorem frontier_of_yardstones
    (y01 : AltStdBalancedOrder2InnerSmall) (y02 : ShapeTwoSmallNine)
    (y03 : ShapeTwoTenNoSwapPartnerNoCentralStdHS) (y04 : ShapeTwoTenSwapPartnerStdHS)
    (y05 : CFSG.EvenSporadicStandard.HSStd.HSSection5)
    (y06 : CFSG.EvenSporadicStandard.TwoHS.HaradaHNRecognitionKP)
    (y07 : CFSG.EvenSporadicStandard.TwoHS.GH312Fixed)
    (y08 : CFSG.ComponentClassification.HarrisLit.Harris82Theorem1SimpleKProperOdd)
    (y09 : SmallF3StandardOddLieU) (y10 : OddLieThm187bResidualL2Ree)
    (y11 : OddLieThm187bResidualHigherRank)
    (y12 : CFSG.ComponentClassification.GrSLit.HeldKSwapped)
    (hCIT : type_of% @CFSG.Milestones.cl_lit_classical_involution_theorem_models)
    (hGH : type_of% @CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models)
    (hU : type_of% @CFSG.Milestones.ctu_kproper_simple_unbalanced_recognition)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (htype : Blueprint.Recognition.Exact.OddStandardType (L ⧸ Subgroup.center L)) :
    (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card G ∈ lieOrdersChar p) ∨
      Nat.card G ∈ standardComponentOddSporadicOrders := by
  have hHS : ShapeTwoTenStdHS :=
    shapeTwoTenStdHS_of_parts' CFSG.SeitzReduction.gls3OddLieAutComponentsInput
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput shapeTwoTenL44Excl_holds
      y03 y04
  have h7 : CFSG.EvenSporadicStandard.TwoHSGivesHN :=
    CFSG.EvenSporadicStandard.Frontier.child7_of_frontier y06 y07
  exact ct_odd_standard_recognition_frontier_of_shapeTwoTen y01
    (shapeTwoSmallTen_of_yardstones y02 hHS y05 h7) hCIT hGH
    (oddLieThm187b_of_harris82_of_mult_of_simpleKProperOdd y08
      (oddLieThm187bResidualMult_of_split y09 y10 y11))
    (kProperSimpleUnbalancedUOutcome_of_milestone hU) y12 G hnonab hK L hL htype

end CFSG.Yardstones.M0362f3a873a3
