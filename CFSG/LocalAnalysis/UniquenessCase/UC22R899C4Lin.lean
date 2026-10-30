module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem uc22r899c4_exists_coord {p : ℕ} [hp : Fact p.Prime] (hp3 : p % 3 ≠ 1) {a b c : ZMod p}
    (hab : a ≠ b) :
    ∃ x y : ZMod p, x * a + y * c = x * b + y * a ∧
      (x * a + y * c ≠ 0 ∨ x * c + y * b ≠ 0) := by
  refine ⟨a - c, a - b, by ring, ?_⟩
  by_contra h
  push Not at h
  obtain ⟨h0, h2⟩ := h
  have hkey : (b - a) ^ 2 * (a ^ 2 + a * b + b ^ 2) = 0 := by
    linear_combination (a ^ 2 + b * c - a * b) * h0 + (-b ^ 2) * h2
  have hq : a ^ 2 + a * b + b ^ 2 = 0 :=
    (mul_eq_zero.1 hkey).resolve_left (pow_ne_zero 2 (sub_ne_zero.2 hab.symm))
  have ha : a ≠ 0 := by
    rintro rfl
    exact hab (pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (by linear_combination hq)).symm
  have hu : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have ht2 : (b * a⁻¹) ^ 2 + b * a⁻¹ + 1 = 0 := by
    linear_combination (a⁻¹) ^ 2 * hq + (-(b * a⁻¹ + 1 + a * a⁻¹)) * hu
  have ht1 : b * a⁻¹ ≠ 1 := fun h => hab ((mul_inv_eq_one₀ ha).1 h).symm
  have ht3 : (b * a⁻¹) ^ 3 = 1 := by linear_combination (b * a⁻¹ - 1) * ht2
  have ht0 : b * a⁻¹ ≠ 0 := by
    intro h0
    rw [h0] at ht2
    norm_num at ht2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf (b * a⁻¹) = 3 := orderOf_eq_prime ht3 ht1
  have hd : 3 ∣ p - 1 := ho ▸ orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one ht0)
  have h2 := hp.out.two_le
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
