module

public import CFSG.Mathlib.GroupTheory.PermCenter

public section

namespace CFSG

theorem perm_eq_one_of_forall_commute {α : Type*} [Finite α] (h : 3 ≤ Nat.card α)
    {σ : Equiv.Perm α} (hσ : ∀ τ : Equiv.Perm α, σ * τ = τ * σ) : σ = 1 := by
  have hc : σ ∈ Subgroup.center (Equiv.Perm α) :=
    Subgroup.mem_center_iff.2 fun τ => (hσ τ).symm
  rwa [center_perm_eq_bot_of_three_le_card h, Subgroup.mem_bot] at hc

end CFSG
