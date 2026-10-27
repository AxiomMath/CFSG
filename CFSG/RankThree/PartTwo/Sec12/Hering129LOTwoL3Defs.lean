module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129L.OTwoL3

@[expose] def E9Q8 (L : Type*) [Group L] : Prop :=
  ∃ x₁ x₂ n₁ n₂ : L, x₁ ^ 3 = 1 ∧ x₂ ^ 3 = 1 ∧ x₁ * x₂ = x₂ * x₁ ∧ x₁ ≠ 1 ∧
    x₂ ∉ Subgroup.zpowers x₁ ∧ n₁ * x₁ * n₁⁻¹ = x₂⁻¹ ∧ n₁ * x₂ * n₁⁻¹ = x₁ ∧
    n₂ * x₁ * n₂⁻¹ = x₁⁻¹ * x₂⁻¹ ∧ n₂ * x₂ * n₂⁻¹ = x₁⁻¹ * x₂

@[expose] def FourGroup (L : Type*) [Group L] : Prop :=
  ∃ a₁ a₂ : L, a₁ ^ 2 = 1 ∧ a₂ ^ 2 = 1 ∧ a₁ ≠ 1 ∧ a₂ ≠ 1 ∧ a₁ ≠ a₂ ∧ a₁ * a₂ = a₂ * a₁

theorem E9Q8.of_mulEquiv {L L' : Type*} [Group L] [Group L'] (e : L ≃* L') (h : E9Q8 L) :
    E9Q8 L' := by
  obtain ⟨x₁, x₂, n₁, n₂, h1, h2, h12, hx1, hx2, r11, r12, r21, r22⟩ := h
  refine ⟨e x₁, e x₂, e n₁, e n₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · rw [← map_mul, ← map_mul, h12]
  · exact fun h => hx1 (e.injective (by rw [h, map_one]))
  · intro h
    apply hx2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, e.injective (by rw [map_zpow, hk])⟩
  · rw [← map_inv, ← map_mul, ← map_mul, r11, map_inv]
  · rw [← map_inv, ← map_mul, ← map_mul, r12]
  · rw [← map_inv, ← map_mul, ← map_mul, r21, map_mul, map_inv, map_inv]
  · rw [← map_inv, ← map_mul, ← map_mul, r22, map_mul, map_inv]

theorem FourGroup.of_mulEquiv {L L' : Type*} [Group L] [Group L'] (e : L ≃* L') (h : FourGroup L) :
    FourGroup L' := by
  obtain ⟨a₁, a₂, h1, h2, ha1, ha2, ha, hc⟩ := h
  refine ⟨e a₁, e a₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · exact fun h => ha1 (e.injective (by rw [h, map_one]))
  · exact fun h => ha2 (e.injective (by rw [h, map_one]))
  · exact fun h => ha (e.injective h)
  · rw [← map_mul, ← map_mul, hc]

end CFSG.RankThree.PartTwo.Sec12.Hering129L.OTwoL3
