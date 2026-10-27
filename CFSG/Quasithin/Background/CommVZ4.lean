module

public import CFSG.Quasithin.Background.Module
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Quasithin.CommVZ4

theorem zpow_eq_one_or_self_of_sq {M : Type*} [Group M] {y : M} (hy : y ^ 2 = 1) (n : ℤ) :
    y ^ n = 1 ∨ y ^ n = y := by
  have h : y ^ n = y ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2]
    rw [zpow_add, zpow_mul, show y ^ (2 : ℤ) = 1 by exact_mod_cast hy, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    rw [h, h0, zpow_zero]
  · right
    rw [h, h1, zpow_one]

theorem exists_mul_inv_apply_ne {K : Type} [CommGroup K] [Finite K]
    (hK : ∀ k : K, k ^ 2 = 1) {g : MulAut K} (hg : g ^ 4 = 1) {κ : K} (hκ : g κ = κ)
    (hcard : 4 ≤ Nat.card (commV (Subgroup.zpowers (g ^ 2)))) :
    ∃ k : K, g k * g⁻¹ k ≠ 1 ∧ g k * g⁻¹ k ≠ κ := by
  by_contra hcon'
  have hcon : ∀ k : K, g k * g⁻¹ k ≠ 1 → g k * g⁻¹ k = κ := fun k hk => by
    by_contra hne
    exact hcon' ⟨k, hk, hne⟩
  have hinv : ∀ k : K, k⁻¹ = k := fun k =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hK k)
  have hS : Nat.card (Subgroup.zpowers κ) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hK κ))
  have hle : commV (Subgroup.zpowers (g ^ 2)) ≤ Subgroup.zpowers κ := by
    unfold commV
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, k, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases zpow_eq_one_or_self_of_sq (y := g ^ 2) (by rw [← pow_mul]; exact hg) n with h | h
    · rw [h]
      simp
    · rw [h]
      have e : (g ^ 2) k * k⁻¹ = g (g k * g⁻¹ k) := by
        rw [map_mul, MulAut.apply_inv_self, hinv k, pow_two, MulAut.mul_apply]
      rw [e]
      by_cases h1 : g k * g⁻¹ k = 1
      · rw [h1, map_one]
        exact one_mem _
      · rw [hcon k h1, hκ]
        exact Subgroup.mem_zpowers κ
  have := Subgroup.card_le_of_le hle
  omega

end CFSG.Quasithin.CommVZ4
