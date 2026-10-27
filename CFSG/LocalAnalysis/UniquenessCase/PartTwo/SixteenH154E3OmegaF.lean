module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_omega_mem_uniqueSet_of_card_prime (D : Data G) {p : ℕ} (hp : p.Prime)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) {A : Subgroup G} (hAM : A ≤ D.M)
    (hAc : Nat.card A = p) : A ∈ uniqueSet D.M := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine uc22p22r_mem_uniqueSet_of_sp D hp hsp hAM
    (IsPGroup.of_card (n := 1) (by rw [hAc, pow_one])) ?_
  intro hA
  rw [hA, Subgroup.card_bot] at hAc
  exact hp.one_lt.ne hAc

theorem s16h_e3_three_mem_uniqueSet (D : Data G) (hSg : UC6S846.SigmaStd D)
    (hns : ¬ Group.IsSolvable ↥D.M) (h3 : 3 ∈ D.sig) {D₃ : Subgroup G} (hD₃M : D₃ ≤ D.M)
    (hD₃c : Nat.card D₃ = 3) : D₃ ∈ uniqueSet D.M :=
  s16h_e3_omega_mem_uniqueSet_of_card_prime D Nat.prime_three
    (UC6S846.sp_of_mem_sig hSg hns h3) hD₃M hD₃c

theorem s16h_e3_seven_mem_uniqueSet (D : Data G) (hU2 : R8100U2 D) (he : evenRank G = 3)
    {L₀ A : Subgroup G} (hL₀ : L₀ ∈ calC D.M) (hc2 : (conjSetOf D.M L₀).ncard = 2)
    (h2₀ : IsL2 (Bar2 L₀) 3) (h3 : 3 ∈ D.sig) (hAc : Nat.card A = 7) (hA : A ≤ L₀) :
    A ∈ uniqueSet D.M :=
  hU2 he L₀ 3 3 7 3 hL₀ hc2 (Or.inl ⟨h2₀, by decide⟩) ⟨1, rfl⟩ dvd_rfl (by norm_num)
    (by norm_num) h3 A hA hAc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
