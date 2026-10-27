module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Realize
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordsSumZero
import CFSG.GroupTheory.WeirSylow.UniqueE27GLFour
import CFSG.GroupTheory.WeirSylow.UniqueE27LinearFour
import CFSG.GroupTheory.WeirSylow.UniqueE27UnitaryFour
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordDefs
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open CFSG.Open
open CFSG.GroupTheory.WeirSylow
  (uniqueElemSylow_statedProj_statedSL_four uniqueElemSylow_statedProj_statedSU_four
   scalar_pow_four_eq_one_of_mem_statedSL)

theorem exists_isSumZeroCoords_of_equiv_statedSL {Y : Type} [Group Y] [Finite Y] {K : Type}
    [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1) (Z : Subgroup Y) [Z.Normal]
    (hZ : ¬ 3 ∣ Nat.card Z) (e : Y ⧸ Z ≃* StatedProj (StatedSL 4 K)) {A : Subgroup Y}
    (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∃ c : Multiplicative (Fin 4 → ZMod 3) →* Y, IsSumZeroCoords A c := by
  obtain ⟨ζ⟩ := CubeRoot.exists_of_dvd h3
  have hN : ¬ 3 ∣ Nat.card ((StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K)) :=
    StatedAPI.not_dvd_card_statedScalars_subgroupOf (StatedSL 4 K) Nat.prime_three
      (by norm_num) fun c hc => scalar_pow_four_eq_one_of_mem_statedSL hc
  exact IsSumZeroCoords.exists_of_model (isSumZeroCoords_statedSL ζ) _ hN
    (uniqueElemSylow_statedProj_statedSL_four h3) Z hZ e hA h27

theorem exists_isSumZeroCoords_of_equiv_statedSU {Y : Type} [Group Y] [Finite Y] {K : Type}
    [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1)
    (Z : Subgroup Y) [Z.Normal] (hZ : ¬ 3 ∣ Nat.card Z)
    (e : Y ⧸ Z ≃* StatedProj (StatedSU 4 q K)) {A : Subgroup Y}
    (hA : IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∃ c : Multiplicative (Fin 4 → ZMod 3) →* Y, IsSumZeroCoords A c := by
  have hq : q ≠ 0 := by omega
  have h3K : 3 ∣ Nat.card K - 1 := by
    have h1 : 1 ≤ q := Nat.pos_of_ne_zero hq
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ h1
    have hd : q + 1 ∣ q ^ 2 - 1 := ⟨q - 1, by zify [h1, h2]; ring⟩
    rw [hK]
    exact h3.trans hd
  obtain ⟨ζ⟩ := CubeRoot.exists_of_dvd h3K
  have hN : ¬ 3 ∣ Nat.card ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 q K)) :=
    StatedAPI.not_dvd_card_statedScalars_subgroupOf (StatedSU 4 q K) Nat.prime_three
      (by norm_num) fun c hc =>
        scalar_pow_four_eq_one_of_mem_statedSL (StatedAPI.statedSU_le_statedSL 4 q K hc)
  exact IsSumZeroCoords.exists_of_model
    (isSumZeroCoords_statedSU (neg_one_pow_eq_neg_one_of_card_eq_sq hK) h3 ζ) _ hN
    (uniqueElemSylow_statedProj_statedSU_four hK h3) Z hZ e hA h27

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
