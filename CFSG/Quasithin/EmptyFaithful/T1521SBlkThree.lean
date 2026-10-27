module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

open Subgroup
open scoped commutatorElement

theorem commutator_commutator_le_of_rotate1521 {G : Type*} [Group G] {N H₁ H₂ H₃ : Subgroup G}
    (hn₁ : H₁ ≤ Subgroup.normalizer (N : Set G)) (hn₂ : H₂ ≤ Subgroup.normalizer (N : Set G))
    (hn₃ : H₃ ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N)
    (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) : ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  have hconj : ∀ g ∈ Subgroup.normalizer (N : Set G), ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have key : ∀ w ∈ ⁅H₁, H₂⁆, w ∈ Subgroup.normalizer (N : Set G) ∧ ∀ z ∈ H₃, ⁅w, z⁆ ∈ N := by
    intro w hw
    have hw' : w ∈ Subgroup.closure {g : G | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁, g₂⁆ = g} := hw
    clear hw
    induction hw' using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hw
      refine ⟨?_, fun z hz => ?_⟩
      · have hxN := hn₁ hx
        have hyN := hn₂ hy
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hxN hyN) (inv_mem hxN)) (inv_mem hyN)
      · have hu : ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ ∈ N := by
          rw [← commutatorElement_inv]
          exact N.inv_mem (h2 (Subgroup.commutator_mem_commutator
            (Subgroup.commutator_mem_commutator (H₃.inv_mem hz) (H₁.inv_mem hx)) hy))
        have hv : ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ ∈ N := by
          rw [← commutatorElement_inv]
          exact N.inv_mem (h1 (Subgroup.commutator_mem_commutator
            (Subgroup.commutator_mem_commutator (H₂.inv_mem hy) hz) (H₁.inv_mem hx)))
        have hxz := mul_mem (hn₁ hx) (hn₃ hz)
        have hxy := mul_mem (hn₁ hx) (hn₂ hy)
        have e1 : ⁅⁅x, y⁆, z⁆ = (x * y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ * (x * y)⁻¹) *
            (x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ * (x * z)⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e1]
        exact mul_mem (hconj _ hxy _ hv) (hconj _ hxz _ hu)
    | one => exact ⟨one_mem _, fun z _ => by simp⟩
    | mul a b _ _ iha ihb =>
      refine ⟨mul_mem iha.1 ihb.1, fun z hz => ?_⟩
      have e1 : ⁅a * b, z⁆ = (a * ⁅b, z⁆ * a⁻¹) * ⁅a, z⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact mul_mem (hconj _ iha.1 _ (ihb.2 z hz)) (iha.2 z hz)
    | inv a _ iha =>
      refine ⟨inv_mem iha.1, fun z hz => ?_⟩
      have e1 : ⁅a⁻¹, z⁆ = a⁻¹ * (⁅a, z⁆)⁻¹ * a := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      have := hconj _ (inv_mem iha.1) _ (N.inv_mem (iha.2 z hz))
      simpa using this
  exact Subgroup.commutator_le.mpr fun w hw z hz => (key w hw).2 z hz

end CFSG.Quasithin
