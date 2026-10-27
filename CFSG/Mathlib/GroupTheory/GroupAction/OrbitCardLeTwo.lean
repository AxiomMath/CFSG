module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Range

public section

namespace CFSG

variable {G α : Type*} [Group G] [MulAction G α]

theorem smul_eq_or_smul_eq_or_smul_eq_smul_of_card_orbit_le_two [Finite G] {x : α}
    (h : Nat.card (MulAction.orbit G x) ≤ 2) (g₁ g₂ : G) :
    g₁ • x = x ∨ g₂ • x = x ∨ g₁ • x = g₂ • x := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h₁, h₂, h₁₂⟩ := hcon
  have hsub : ({x, g₁ • x, g₂ • x} : Set α) ⊆ MulAction.orbit G x := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h | h
    · rw [h]; exact MulAction.mem_orbit_self x
    · rw [h]; exact MulAction.mem_orbit x g₁
    · rw [h]; exact MulAction.mem_orbit x g₂
  have hcard : ({x, g₁ • x, g₂ • x} : Set α).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨x, g₁ • x, g₂ • x, Ne.symm h₁, Ne.symm h₂, h₁₂, rfl⟩
  have hfin : (MulAction.orbit G x).Finite := Set.finite_range _
  have hle : 3 ≤ (MulAction.orbit G x).ncard := by
    calc 3 = ({x, g₁ • x, g₂ • x} : Set α).ncard := hcard.symm
      _ ≤ (MulAction.orbit G x).ncard := Set.ncard_le_ncard hsub hfin
  rw [Nat.card_coe_set_eq] at h
  exact (Nat.not_le_of_gt (Nat.lt_succ_self 2)) (Nat.le_trans hle h)

end CFSG
