module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Torus
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3U4Order
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3U4Type
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3U4Fix
import CFSG.Quasithin.H13.U4ParModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type} [Field K]

theorem sylow_three_hypSU_two_zero (h : UnitaryFieldData 2 n K) (hn : Even n) :
    IsPGroup 3 (torusPow h 2 0 (3 ^ (Nat.card Kˣ).factorization 3)) ∧
      ¬ 3 ∣ (torusPow h 2 0 (3 ^ (Nat.card Kˣ).factorization 3)).index ∧
      OmegaNine (hypSU h 2 0) (torusPow h 2 0 (3 ^ (Nat.card Kˣ).factorization 3)) ∧
      FixOmega (hypSU h 2 0) (torusPow h 2 0 (3 ^ (Nat.card Kˣ).factorization 3)) := by
  have := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (torusPow h 2 0 (3 ^ (Nat.card Kˣ).factorization 3)) =
      3 ^ (Nat.card (hypSU h 2 0)).factorization 3 := by
    rw [card_torusPow h 2 0 (three_pow_factorization_dvd h hn),
      factorization_card_hypSU_two_zero h hn, ← pow_mul, mul_comm]
  have h3 : 3 ∣ 3 ^ (Nat.card Kˣ).factorization 3 :=
    dvd_pow_self 3 (Nat.one_le_iff_ne_zero.mp (one_le_factorization_card_units h))
  have hle := torusPow_le_of_dvd h 2 0 h3
  refine ⟨(Sylow.ofCard _ hcard).isPGroup', (Sylow.ofCard _ hcard).not_dvd_index,
    ⟨torusPow h 2 0 3, hle, isElemAbelian_torusPow h 2 0 3, ?_,
      fun s hs hs3 => mem_torusPow_of_pow_eq_one hs hs3⟩, ?_⟩
  · rw [card_torusPow h 2 0 (three_dvd_two_pow_sub_one hn)]
    norm_num
  intro α hα hS s hs hs3
  have hT : ∀ t ∈ torusPow h 2 0 3, α t ∈ torusPow h 2 0 3 := fun t ht =>
    mem_torusPow_of_pow_eq_one (hS t (hle ht))
      (by rw [← map_pow, pow_eq_one_of_mem_torusPow ht, map_one])
  exact eq_of_mem_torusPow_three h hn α hα hT
    (det_sub_one_map_eq_zero_iff h le_rfl zero_le_one
      (CFSG.Quasithin.H13.U4Par.hypScalars_eq_bot h) α)
    (mem_torusPow_of_pow_eq_one hs hs3)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3
