module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3OmegaF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_sl28_uniqueSet_subgroups (D : Data G) (S : s16h_Std D)
    (hU2 : R8100U2 D) (he : evenRank G = 3) (h3 : 3 ∈ D.sig)
    {L₀ : Subgroup G} (hL0 : L₀ ∈ calC D.M) (hc2 : (conjSetOf D.M L₀).ncard = 2)
    (h20 : IsL2 (Bar2 L₀) 3) :
    ∃ D₃ A : Subgroup G,
      D₃ ≤ L₀ ∧ Nat.card D₃ = 3 ∧ D₃ ∈ uniqueSet D.M ∧
      A ≤ L₀ ∧ Nat.card A = 7 ∧ A ∈ uniqueSet D.M := by
  classical
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL0
  have h3bar : 3 ∣ Nat.card (Bar2 L₀) := by
    rw [S17.card_of_isL2 h20]
    norm_num
  have h7bar : 7 ∣ Nat.card (Bar2 L₀) := by
    rw [S17.card_of_isL2 h20]
    norm_num
  obtain ⟨D₃, hD₃le, hD₃c⟩ :=
    s13_exists_subgroup_of_dvd_card_bar (L := L₀) (r := 3) Nat.prime_three h3bar
  obtain ⟨A, hAle, hAc⟩ :=
    s13_exists_subgroup_of_dvd_card_bar (L := L₀) (r := 7) (by norm_num) h7bar
  refine ⟨D₃, A, hD₃le, hD₃c, ?_, hAle, hAc, ?_⟩
  · exact s16h_e3_three_mem_uniqueSet D S.hSig hns h3 (hD₃le.trans hL0.1.le) hD₃c
  · exact s16h_e3_seven_mem_uniqueSet D hU2 he hL0 hc2 h20 h3 hAc hAle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
