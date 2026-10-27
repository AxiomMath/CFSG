module

public import CFSG.Yardstones.M41b0c98b3153.Definitions
public import CFSG.Milestones.CT_Seitz_centerless_reduction_frontier
public import CFSG.LocalAnalysis.EvenBN.LinearThree.MainCaseA
public import CFSG.LocalAnalysis.EvenBN.U4.Final
public import CFSG.LocalAnalysis.EvenBN.TwoF4.Exclusion
public import CFSG.LocalAnalysis.EvenBN.U5.Main
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialSmall
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatDispatch

public section

namespace CFSG.Yardstones.M41b0c98b3153

open Subgroup CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.EvenBN

theorem u5CenterlessExclusion_of_cases (hA : U5LinearCaseExclusion)
    (hB : U5ProductCaseExclusion) : U5.CenterlessExclusion := by
  intro G _ _ L f hs
  obtain ⟨K, _, h, d, -, hd⟩ := U5.Data.exists_hyp hs
  by_cases hM : d.M₂Linear
  · exact hA G f K h d hd hM
  · exact hB G f K h d hd hM

theorem g2CenterlessExclusion_of_cases (h₂ : G2FourCenterlessExclusion)
    (h₃ : G2LargeCenterlessExclusion) : G2.G2CenterlessExclusion := by
  intro G _ _ _ hnonab hK L hL hZ hcore hS f hf hm
  rcases Nat.lt_or_ge f 3 with h | h
  · obtain rfl : f = 2 := by omega
    exact h₂ G hnonab hK L hL hZ hcore hS hm
  · exact h₃ G hnonab hK L hL hZ hcore hS f h hm

theorem trialityD4CenterlessExclusion_of_cases (h₁ : TrialityD4TwoCenterlessExclusion)
    (h₂ : TrialityD4LargeCenterlessExclusion) : TrialityD4.TrialityD4CenterlessExclusion := by
  intro G _ _ _ hnonab hK L hL hZ hcore hS f hf hm
  rcases Nat.lt_or_ge f 2 with h | h
  · obtain rfl : f = 1 := by omega
    exact h₁ G hnonab hK L hL hZ hcore hS hm
  · exact h₂ G hnonab hK L hL hZ hcore hS f h hm

theorem ct_even_standard_residual_reduction_of_yardstones
    (h01 : U5LinearCaseExclusion)
    (h02 : U5ProductCaseExclusion)
    (h03 : UnitaryFiveTwo.GomiU42Input)
    (h04 : UnitaryFiveTwo.GomiLemma1PInput)
    (h05 : U52UnitaryCaseExclusion)
    (h06 : U52LinearSmallCentralizerExclusion)
    (h07 : Sp4.SingleCommutatorExclusion)
    (h08 : Sp4.BothTrivialCases.BothTrivialProductExclusion)
    (h09 : Sp4.BothTrivialCases.BothTrivialOddFieldNoSwap)
    (h10 : G2FourCenterlessExclusion)
    (h11 : G2LargeCenterlessExclusion)
    (h12 : TrialityD4TwoCenterlessExclusion)
    (h13 : TrialityD4LargeCenterlessExclusion)
    (h14 : Tits.Thm49FailureExclusion)
    (h15 : TitsThm49StatementExclusion) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
      ∀ L : Subgroup G, standardComponentIsStandard L →
      (∀ t : G, orderOf t = 2 →
        standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥) →
      ∀ S : Sylow 2 (Subgroup.centralizer (L : Set G)),
        IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))) →
        Recognition.Exact.EvenStandardType (L ⧸ Subgroup.center L) →
        ¬ Recognition.Exact.EvenStandardException (L ⧸ Subgroup.center L) →
        Recognition.Exact.EvenStandardResidual L := by
  have hsel : GMSK.FixedRootSelector fun D _ => Catalog D :=
    GMSK.catalog_selector GMSK.fixedRootSelector_alternating GMSK.fixedRootSelector_oddLieType
      GMSK.fixedRootSelector_evenLieType GMSK.Sporadic.fixedRootSelector_sporadicRep
  have hPSp2 := Sp4.bnFamily_PSp2_of_sectors h07
    (Sp4.BothTrivialCases.bothTrivialExclusion_of_cases hsel
      Sp4.BothTrivialLayer.smallSurvivorsNoElementary h08 h09)
  have hU52 : UnitaryFiveTwo.U52CenterlessExclusion :=
    UnitaryFiveTwo.u52CenterlessExclusion_of_hyp fun G _ _ d hd => by
      rcases hd.kLinear_or_kUnitary h03 with hK | hK
      · by_cases hH : d.H ≤ d.L ⊔ zpowers d.t
        · exact h06 G d hd hK hH
        · exact hd.false_of_gomiLemma1P hPSp2 h04 hK hH
      · exact h05 G d hd hK
  have hTits : Tits.TitsCenterlessExclusion :=
    Tits.titsCenterlessExclusion_of_data fun G _ _ d hd => h15 G d hd (hd.thm49Statement h14)
  have hBN : CFSG.LocalAnalysis.ComponentInitial.EvenResidual.BNRankTwoCenterStatement :=
    CFSG.LocalAnalysis.ComponentInitial.EvenResidual.bnRankTwoCenter_of_families
      LinearThree.ctt_bn_psl3 U4.bnFamily_PSU4 (UnitaryFiveTwo.bnFamily_PSU5two_of_exclusion hU52)
      (U5.bnFamily_PSU5_of_exclusion (u5CenterlessExclusion_of_cases h01 h02)) hPSp2
      (G2.bnFamily_G2_of_exclusion (g2CenterlessExclusion_of_cases h10 h11))
      (TrialityD4.bnFamily_trialityD4_of_exclusion
        (trialityD4CenterlessExclusion_of_cases h12 h13))
      TwoF4.bnFamily_twistedF4 (Tits.bnFamily_Tits_of_exclusion hTits)
  exact CFSG.LocalAnalysis.ComponentInitial.EvenResidual.even_standard_residual_of_frontiers
    CFSG.Milestones.ct_seitz_centerless_reduction_frontier hBN

end CFSG.Yardstones.M41b0c98b3153
