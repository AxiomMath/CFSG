module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestCtrl

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

variable {K : Type} [Group K]

theorem SporKRestControlsAt.mem_of_path {x z h g : K} {Y : Subgroup K}
    (hY : SporKRestControlsAt x Y) (hx : x ∈ Y) (hxh : x * h = h * z) (hxz : x * z = z * x)
    (hzw : z * (g⁻¹ * x * g) = g⁻¹ * x * g * z) : g ∈ Y := by
  have hzY : z ∈ Y := hY.mem_of_comm hx hxz.symm
  have hz : h⁻¹ * x * h = z := by rw [mul_assoc, hxh, ← mul_assoc, inv_mul_cancel, one_mul]
  have hhY : h ∈ Y := hY h (by rw [hz]; exact hzY)
  have hw : (g⁻¹ * x * g)⁻¹ * z * (g⁻¹ * x * g) = z := by
    rw [mul_assoc, hzw, ← mul_assoc, inv_mul_cancel, one_mul]
  have hwY : g⁻¹ * x * g ∈ Y := hY.mem_of_conj hhY hxh (by rw [hw]; exact hzY)
  exact hY g hwY

theorem sporKRest_generating_of_paths [Finite K] {p : ℕ} (hp : p.Prime) (a b : K)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) {x : K} (hx : x ^ p = 1)
    (ha : ∃ z h : K, x * h = h * z ∧ x * z = z * x ∧ z * (a⁻¹ * x * a) = a⁻¹ * x * a * z)
    (hb : ∃ z h : K, x * h = h * z ∧ x * z = z * x ∧ z * (b⁻¹ * x * b) = b⁻¹ * x * b * z) :
    SporKRestGenerating p x := by
  intro Y hS hY
  have hxY : x ∈ Y := hY.mem_self hp hx hS
  obtain ⟨z₁, h₁, e₁, c₁, d₁⟩ := ha
  obtain ⟨z₂, h₂, e₂, c₂, d₂⟩ := hb
  have haY : a ∈ Y := hY.mem_of_path hxY e₁ c₁ d₁
  have hbY : b ∈ Y := hY.mem_of_path hxY e₂ c₂ d₂
  rw [eq_top_iff, ← hab, Subgroup.closure_le]
  rintro w (rfl | rfl)
  · exact haY
  · exact hbY

end CFSG.StandardType.SporadicShape

end
