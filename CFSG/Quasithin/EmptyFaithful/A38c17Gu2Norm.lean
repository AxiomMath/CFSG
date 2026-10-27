module

public import CFSG.LieType.Steinberg.CentralExt.UnitaryField

public section

namespace CFSG.Quasithin.A38c17

open CFSG.LieType.Steinberg CFSG.LieType.BorelTits

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] [CharP K p]

theorem exists_norm_eq_fixedSubfield (hK : Nat.card K = p ^ 2) (a : fixedSubfield K p 1) :
    ∃ y : K, unitaryInvolution K p 1 y * y = (a : K) := by
  have hK' : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
  by_cases h0 : (a : K) = 0
  · exact ⟨0, by rw [h0, mul_zero]⟩
  · exact CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hK'
      (mem_fixedSubfield.mp a.2) h0

theorem exists_eq_mul_of_norm_eq_one (hK : Nat.card K = p ^ 2) {Δ : K}
    (hΔ : unitaryInvolution K p 1 Δ * Δ = 1) :
    ∃ l : K, l ≠ 0 ∧ unitaryInvolution K p 1 l = Δ * l := by
  have hK' : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
  have hinv : ∀ c : K, unitaryInvolution K p 1 (unitaryInvolution K p 1 c) = c :=
    unitaryInvolution_involutive hK'
  have hΔ0 : Δ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hΔ
    exact zero_ne_one hΔ
  have hσΔ : unitaryInvolution K p 1 Δ = Δ⁻¹ := eq_inv_of_mul_eq_one_left hΔ
  have key : ∀ x : K, unitaryInvolution K p 1 (x + Δ⁻¹ * unitaryInvolution K p 1 x) =
      Δ * (x + Δ⁻¹ * unitaryInvolution K p 1 x) := by
    intro x
    rw [map_add, map_mul, map_inv₀, hσΔ, inv_inv, hinv, mul_add, ← mul_assoc,
      mul_inv_cancel₀ hΔ0, one_mul, add_comm]
  by_cases hneg : Δ = -1
  · obtain ⟨a, ha⟩ := exists_unitaryInvolution_ne hK'
    refine ⟨a + Δ⁻¹ * unitaryInvolution K p 1 a, fun h => ha ?_, key a⟩
    rw [hneg, inv_neg, inv_one] at h
    linear_combination -h
  · refine ⟨1 + Δ⁻¹ * unitaryInvolution K p 1 1, fun h => hneg ?_, key 1⟩
    rw [map_one, mul_one] at h
    rw [← inv_inv Δ, eq_neg_of_add_eq_zero_right h, inv_neg, inv_one]

end CFSG.Quasithin.A38c17
