module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.SetTheory.Cardinal.Finite


public section

namespace CFSG

open Equiv

theorem center_perm_eq_bot_of_three_le_card {α : Type*} [Finite α] (h : 3 ≤ Nat.card α) :
    Subgroup.center (Equiv.Perm α) = ⊥ := by
  classical
  have : Fintype α := Fintype.ofFinite α
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  ext x
  by_contra hx
  rw [Equiv.Perm.coe_one, id_eq] at hx
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({x, g x} : Finset α)) (t := Finset.univ)
    (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact lt_of_le_of_lt Finset.card_le_two (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  have hc : g * swap x z = swap x z * g := (Subgroup.mem_center_iff.mp hg (swap x z)).symm
  rw [mul_swap_eq_swap_mul] at hc
  have he := congrArg (fun σ : Equiv.Perm α => σ (g x)) (mul_right_cancel hc)
  simp only [swap_apply_left, swap_apply_of_ne_of_ne hx (Ne.symm hz.2)] at he
  exact hz.1 (g.injective he)

end CFSG
