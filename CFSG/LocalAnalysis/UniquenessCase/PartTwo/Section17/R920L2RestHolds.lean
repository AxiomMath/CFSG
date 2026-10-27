module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2OddFinal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2OddKFactL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2NSCalH
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2Main
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7UseThree
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem r920L2Rest_of_inputs (hK462 : UCK.K462)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hK : UCK.K332Cyc) (hKM : K332Meta)
    (D : Data G) (h63 : UC6.R6_3 D) (h82 : F08.R82 D) (hSg : UC6S846.SigmaStd D)
    (hKF7 : KF7Use D) (h912 : F09.R912L2 D) (hR92 : F09.R92 D) (hC : R920L2OddY2 D) :
    R920L2Rest D := by
  intro L D₃ n hL hD₃L hD₃ hD₃U hL2 _ hσ hcase
  by_cases hU : UniqueMax D.M L
  · exact Or.inl hU
  rcases hcase with ⟨hodd, hn5, ⟨A, hAU, hAL, hAp, hAdvd⟩, p, hp, hpd⟩ | ⟨hev, hnsp⟩
  · exfalso
    have hY2 : L ∈ F09.calY2_9 D := by
      by_cases hsp : IsStronglyPEmbedded 3 D.M
      · exact (uniqueMax_or_mem_calY2_of_sp D h63 hsp hL hL2).resolve_left hU
      · exact (uniqueMax_or_mem_calY2_of_not_sp hK (fun _ => hKM) h82 hSg hKF7 hsp hL hL2
          (by omega) hσ hD₃L hD₃ hD₃U).resolve_left hU
    exact hC L D₃ A n hL hL2 hodd hn5 hD₃L hD₃ hD₃U hAU hAL hAp hAdvd hY2
  · obtain ⟨m, rfl⟩ := hev
    have hm2 : 2 ≤ m + m := uc22p20g_two_le_of_isL2 hL2
    rcases Nat.lt_or_ge 1 m with hm1 | hm1
    · exfalso
      have hL2' : IsL2 (Bar2 L) (2 * m) := by rwa [two_mul]
      rcases uniqueMax_or_mem_calY2_of_not_sp hK (fun _ => hKM) h82 hSg hKF7 hnsp hL hL2
          (by omega) hσ hD₃L hD₃ hD₃U with h | h
      · exact hU h
      · exact false_of_mem_calY2_of_isL2_even hK462 hSch D h912 hR92 hL hm1 hL2' h
    · have hm : m = 1 := by omega
      subst hm
      exact Or.inr (isAlt_five_of_isL2_two hL2)

theorem r920L2Rest_dataOfSetup
    (hSQ : PartOne.Section7.StronglyEmbeddedSolvableQ) (hSE : PartOne.Section7.StronglyEmbeddedFive)
    (hK3 : PartOne.Section7.StronglyEmbeddedThree) (hK462 : UCK.K462) (hK32 : UCK.K32)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hK : UCK.K332Cyc) (hKM : K332Meta)
    (h63c : CFSG.CGT.PushingUpLit.CGT6.AschbacherSixThreeCore)
    (hS : CFSG.LocalAnalysis.RankThreeUC.Standing G) (S : CFSG.LocalAnalysis.RankThreeUC.Setup G)
    (h63 : UC6.R6_3 (Three.dataOfSetup hS S)) (h640 : UC6.R6_40_1 (Three.dataOfSetup hS S))
    (h82 : F08.R82 (Three.dataOfSetup hS S)) :
    R920L2Rest (Three.dataOfSetup hS S) :=
  r920L2Rest_of_inputs hK462 hSch hK hKM _
    h63 h82 (UC6S846.sigmaStd_dataOfSetup hS S)
    (UC22.kf7Use_dataOfSetup hSQ hSE hK3 hS S)
    (F09.r912L2_of_inputs _ (F09.r99_holds _) (F09.r910_holds _)
      (F09.r911_of h63c _ h640) (F09.r9R5_holds _))
    (F09.r92_of_inputs hK32 hSch _)
    (r920L2OddY2_of_inputs _ h63c h640 hK32 hK462 hSch kFactShape92L2Odd_holds)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
