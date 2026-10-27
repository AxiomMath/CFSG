module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem s16c2m_exists_mul_of_mem_sup {A : Type*} [Group A] {K L : Subgroup A}
    (hcomm : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) {x : A} (hx : x ∈ K ⊔ L) :
    ∃ k ∈ K, ∃ l ∈ L, k * l = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ k ∈ K, ∃ l ∈ L, k * l = x)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, L.one_mem, mul_one y⟩
    · exact ⟨1, K.one_mem, y, hy, one_mul y⟩
  · exact ⟨1, K.one_mem, 1, L.one_mem, mul_one 1⟩
  · intro y z hy hz hyz hyz'
    obtain ⟨k₁, hk₁, l₁, hl₁, rfl⟩ := hyz
    obtain ⟨k₂, hk₂, l₂, hl₂, rfl⟩ := hyz'
    refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, l₁ * l₂, L.mul_mem hl₁ hl₂, ?_⟩
    calc (k₁ * k₂) * (l₁ * l₂) = k₁ * (k₂ * l₁) * l₂ := by group
      _ = k₁ * (l₁ * k₂) * l₂ := by rw [hcomm k₂ hk₂ l₁ hl₁]
      _ = (k₁ * l₁) * (k₂ * l₂) := by group
  · intro y hy hyz
    obtain ⟨k, hk, l, hl, rfl⟩ := hyz
    refine ⟨k⁻¹, K.inv_mem hk, l⁻¹, L.inv_mem hl, ?_⟩
    calc k⁻¹ * l⁻¹ = (l * k)⁻¹ := by group
      _ = (k * l)⁻¹ := by rw [hcomm k hk l hl]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
