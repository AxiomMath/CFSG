module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (R920odd)

variable {G : Type} [Group G] [Finite G]

theorem thm1422_of_r920odd {D : Data G} (h1421 : Thm1421 D) (hSg : UC6S846.SigmaStd D)
    (h920 : R920odd D) : Thm1422 D := by
  intro L₁ L₂ X h L hL K hKL hLK
  obtain ⟨hLC, hshape⟩ := Hyp141.mem_isL3 h hL
  have hKM : K ≤ D.M := hKL.trans (CFSG.Quasithin.A3.subnormal_le hLC.1)
  haveI := D.standing.simple
  have hMne : D.M ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab D.maxLocal.1
  refine calNOf_eq_singleton_of_forall_le hMne hKM ?_
  intro H hHne hKH
  by_contra hHM
  obtain ⟨P, hPK, hPsyl⟩ :=
    exists_isSylowOf_le Nat.prime_three (by norm_num) hKL hLK
  have hPL : P ≤ L := hPK.trans hKL
  have hcardP : Nat.card P = 3 := card_sylow_three_of_isL3_bar2 hshape hPsyl
  have hPmem : P ∈ uniqueSet D.M :=
    Hyp141.card_three_mem_uniqueSet h h1421 hL hPL hcardP
  have hyp : Hyp919c D L P K H := by
    unfold Hyp919c
    refine ⟨hLC, hPL, hcardP, hPmem, hKM, ?_, ?_, ?_, hHne, hKH, hHM⟩
    · rw [inf_eq_right.mpr hKL]; exact hLK
    · rw [inf_eq_right.mpr hKL, Subgroup.subgroupOf_self]
      exact inferInstance
    · refine ⟨0, ?_⟩
      rw [inf_eq_right.mpr hKL, Subgroup.subgroupOf_self, Subgroup.index_top]
      norm_num
  obtain ⟨eKL⟩ : Nonempty (Bar2 L ≃* Bar2 K) :=
    CFSG.RankThree.PartTwo.Sec17.Proof17Res3.nonempty_quotient_pCore_two_equiv hKL hLK
  have hL27 : IsL2Odd (Bar2 K) 7 :=
    CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism (Bar2 K)
      (CFSG.Blueprint.LieModel.of_mulEquiv eKL hshape)
  obtain ⟨A, hAK, hApr, hAodd, hnotN⟩ :=
    h920 L P K H hyp hKL 7 (by norm_num) (by norm_num) hL27
  exact hnotN (Hyp141.normalizer_le_of_odd_prime_card h h1421 hSg hL (hAK.trans hKL) hApr hAodd)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
