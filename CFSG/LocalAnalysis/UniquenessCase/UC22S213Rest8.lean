module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest7
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Torus
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Small
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213List
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvable StronglyEmbeddedThree BadNoStrongThree)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3Rest8 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ S21_3Closed L → ¬ S21_3Closed2 L →
    ¬ S21_3ClosedZ L → ¬ S21_3ClosedCov D.M L → ¬ S21_3ClosedSpor D.M L →
    ¬ S21_3ClosedL2 L → ¬ S21_3ClosedTorus L → ¬ S21_3ClosedSmall D.M L → S21_3List L →
    ¬ F08.Thin8 L → CFSG.Open.pRank 3 L ≤ 2 →
    (IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1) →
    ∀ a ∈ c.B, (orderOf a).Prime →
      (∀ p ∈ D.sig,
        CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1) →
      ¬ CentralizesBar a L

section Rest8

set_option linter.unusedSectionVars false

theorem s21_3Rest7_of_rest8 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hσ : S.InMSigma) (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive)
    (hSS : StronglyEmbeddedSolvable) (hK3 : StronglyEmbeddedThree) (hB : BadNoStrongThree)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hGA : GriessAllModelsStatement) (h33 : UCK.K33)
    (h31 : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactThreeRankOneSimple)
    (Ch : Choice2011 G) (h : S21_3Rest8 (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_3Rest7 (UC6.dataOfSetup4 hS hU S) Ch := by
  intro hH c L hL hC hC2 hCZ hCov hSp hL2 hthin h3 hk1 a ha hpr hN
  by_cases hT : S21_3ClosedTorus L
  · exact uc22s213_not_centralizesBar_of_torus hS hU S hσ hPart hSE hSS hK3 hB hOut Ch hH c hL
      hT ha hpr hN
  by_cases hs : S21_3ClosedSmall (UC6.dataOfSetup4 hS hU S).M L
  · exact uc22s213_not_centralizesBar_of_small hS hU S hσ hSE hOut hGA hL hs h3 hk1
      (uc22p21d_odd_orderOf_of_mem_calB1 c.hB ha) hpr (hN S.p S.hp)
  exact h hH c L hL hC hC2 hCZ hCov hSp hL2 hT hs
    (uc22s213_list_of_calC h33 h31 hL hL2 hthin h3) hthin h3 hk1 a ha hpr hN

end Rest8

end CFSG.LocalAnalysis.UniquenessCase.UC22
