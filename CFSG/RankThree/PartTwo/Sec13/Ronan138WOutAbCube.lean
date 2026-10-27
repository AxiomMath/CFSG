module

import CFSG.RankThree.PartTwo.Sec14.Ronan148WFieldE27Cyc
import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Ring.Aut
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138W

theorem eq_one_or_eq_or_eq_sq {K : Type*} [Field K] {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {z : K} (hz : z ^ 3 = 1) : z = 1 ∨ z = ω ∨ z = ω ^ 2 := by
  have h1 : 1 + ω + ω ^ 2 = 0 := by
    have h : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hω
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hω1)
  have hp : (z - 1) * (z - ω) * (z - ω ^ 2) = 0 := by
    linear_combination hz + (z - z ^ 2) * h1 + (z - 1) * hω
  rcases mul_eq_zero.mp hp with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

theorem apply_eq_of_pow_three_eq_one {K : Type*} [Field K] {σ : K ≃+* K} {k : ℕ}
    (hσ : σ ^ 3 ^ k = 1) {ω : K} (hω : ω ^ 3 = 1) : σ ω = ω := by
  by_cases hω1 : ω = 1
  · rw [hω1, map_one]
  have hσω3 : σ ω ^ 3 = 1 := by rw [← map_pow, hω, map_one]
  rcases eq_one_or_eq_or_eq_sq hω hω1 hσω3 with h | h | h
  · exact absurd (σ.injective (h.trans (map_one σ).symm)) hω1
  · exact h
  · exfalso
    have hσ2 : (σ ^ 2) ω = ω := by
      rw [pow_two, RingAut.mul_apply, h, map_pow, h, ← pow_mul]
      calc ω ^ (2 * 2) = ω ^ 3 * ω := by ring
        _ = ω := by rw [hω, one_mul]
    have hpow : ∀ j : ℕ, (σ ^ (2 * j + 1)) ω = ω ^ 2 := by
      intro j
      induction j with
      | zero => simpa using h
      | succ j ih =>
        rw [show 2 * (j + 1) + 1 = 2 + (2 * j + 1) by ring, pow_add, RingAut.mul_apply, ih,
          map_pow, hσ2]
    obtain ⟨j, hj⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    have h1 := hpow j
    rw [← hj, hσ, RingAut.one_apply] at h1
    apply hω1
    have hω0 : ω ≠ 0 := by
      rintro rfl
      norm_num at hω
    have : ω * ω = ω * 1 := by rw [mul_one, ← pow_two, ← h1]
    exact mul_left_cancel₀ hω0 this

theorem exists_cube_eq_mul_inv_of_cyclic {H : Type*} [CommGroup H] [Finite H] [IsCyclic H]
    (f : H →* H) (hf : ∀ y : H, y ^ 3 = 1 → f y = y) (x : H) : ∃ c : H, c ^ 3 = f x * x⁻¹ := by
  by_cases h3 : 3 ∣ Nat.card H
  · obtain ⟨m, hm⟩ := h3
    rw [Sec14.Ronan148W.exists_cube_iff_pow_eq_one hm]
    have hxm : (x ^ m) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, ← hm]
      exact pow_card_eq_one'
    rw [mul_pow, ← map_pow, hf _ hxm, inv_pow, mul_inv_cancel]
  ·
    have hcop : Nat.Coprime 3 (Nat.card H) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    obtain ⟨c, hc⟩ := (powCoprime hcop.symm).surjective (f x * x⁻¹)
    exact ⟨c, hc⟩

end CFSG.RankThree.PartTwo.Sec13.Ronan138W
