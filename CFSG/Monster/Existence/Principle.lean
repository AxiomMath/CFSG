module

public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

public section

namespace CFSG.Monster.Existence

open Subgroup

variable {G : Type*} [Group G]

theorem mem_of_conj_eq {M : Subgroup G} {x g m₁ m₂ : G} (hC : centralizer {x} ≤ M)
    (h₁ : m₁ ∈ M) (h₂ : m₂ ∈ M) (hg : g * (m₁ * x * m₁⁻¹) * g⁻¹ = m₂ * x * m₂⁻¹) : g ∈ M := by
  have hc : m₂⁻¹ * g * m₁ ∈ centralizer {x} := by
    rw [mem_centralizer_singleton_iff]
    calc m₂⁻¹ * g * m₁ * x = m₂⁻¹ * (g * (m₁ * x * m₁⁻¹) * g⁻¹) * (g * m₁) := by group
      _ = m₂⁻¹ * (m₂ * x * m₂⁻¹) * (g * m₁) := by rw [hg]
      _ = x * (m₂⁻¹ * g * m₁) := by group
  have hm := M.mul_mem (M.mul_mem h₂ (hC hc)) (M.inv_mem h₁)
  rwa [show m₂ * (m₂⁻¹ * g * m₁) * m₁⁻¹ = g by group] at hm

theorem centralizer_conj_le_of_mem {M : Subgroup G} {x m : G} (hC : centralizer {x} ≤ M)
    (hm : m ∈ M) : centralizer {m * x * m⁻¹} ≤ M := fun g hg =>
  mem_of_conj_eq hC hm hm (by rw [mem_centralizer_singleton_iff.1 hg, mul_inv_cancel_right])

end CFSG.Monster.Existence
