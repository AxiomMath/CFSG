module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S206y
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
import CFSG.LocalAnalysis.UniquenessCase.UC22S206k
import CFSG.LocalAnalysis.UniquenessCase.UC22S206n

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.H13.A7Blk (ptCore ptPre ptCore_le_ptPre)


variable {G : Type} [Group G] [Finite G]

theorem s20_6_dataOfSetup_of_r880J4 (hK331 : InS3.K331) (hS : Standing G) (S : Setup G)
    (hSg : UC6S846.SigmaStd (dataOfSetup hS S)) (h76 : F07.R76Sig (dataOfSetup hS S))
    (h82 : F08.R82 (dataOfSetup hS S)) (hJ4 : F08.R880J4 (dataOfSetup hS S)) :
    S20_6 (dataOfSetup hS S) := by
  intro h1930 L hL h9
  set D := dataOfSetup hS S
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hk, α, hα, hker, i, -, hLM, hTK, -⟩ := uc22s206b_by1930 D
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput listBNonabelian h1930 hL h9
  have hLM' : L ⊓ S.M = ptPre α i := hLM
  have hKM : ptCore α i ≤ D.M := (ptCore_le_ptPre α i).trans (hLM'.symm.le.trans inf_le_right)
  have hchar : S.M ⊓ centralizer (pCoreOf 2 S.M : Set G) ≤ pCoreOf 2 S.M :=
    hS.charTwo S.M S.witness.maxLocal.1
  have hβ : ∀ p : ℕ, p ∉ uniqueFourBeta G := by
    rintro p ⟨hp, hp2, -, h4⟩
    have hle : uniqueFourTwoLocalRank p G ≤ 3 := by
      refine csSup_le' ?_
      rintro _ ⟨H, hH, rfl⟩
      exact (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank p hp hp2 H hH).trans
        hS.rank.le
    omega
  have hU : uniqueFourUnique G := fun _ _ ⟨p, hp⟩ => absurd hp.1 (hβ p)
  by_cases hF : ⁅((ptCore α i).subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)),
      CFSG.fittingSubgroup (Bar2 D.M)⁆ = ⊥
  swap
  · exact uc22s206k_false hU S.witness.maxLocal hchar α hα hker hLM' hF
      fun p hp => absurd hp.1 (hβ p)
  by_cases hNc : ∀ J : Subgroup (Bar2 D.M), IsComponentOf J ⊤ →
      ((ptCore α i).subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ≤
        normalizer (J : Set (Bar2 D.M))
  swap
  · push Not at hNc
    exact uc22s206n_false hU S.witness.maxLocal hchar α hα hker hLM' hNc
      fun p hp => absurd hp.1 (hβ p)
  have h3 : CFSG.Open.pRank 3 D.M ≤ 3 :=
    (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) S.M S.witness.maxLocal.1).trans hS.rank.le
  exact uc22s206y_false D hSg h76 hJ4 hK331 uc22p20r_nativeGriess h82 hk h3 α hα hker hLM' hKM
    hTK hF hNc fun J hJ =>
      uc22s206t_outSolvable D CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds hJ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
