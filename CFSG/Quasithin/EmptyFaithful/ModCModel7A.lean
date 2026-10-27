module

public import CFSG.Quasithin.EmptyFaithful.ModCModel7Defs

public section

namespace CFSG.Quasithin.ModC

open Equiv Equiv.Perm CFSG.Quasithin.G6

namespace M7

set_option maxRecDepth 100000

theorem elts_nodup : elts.Nodup := by decide +kernel

theorem elts_length : elts.length = 8 := by decide +kernel

theorem gens_inv : ∀ s ∈ gens, s⁻¹ = s := by decide +kernel

theorem elts_closed : ∀ s ∈ gens, ∀ y ∈ elts, s * y ∈ elts := by decide +kernel

theorem gens_even : ∀ s ∈ gens, sign s = 1 := by decide +kernel

theorem D0_even : ∀ s ∈ D0, sign s = 1 := by
  have h : D0 ≤ (sign : Perm (Fin 7) →* ℤˣ).ker := by
    refine Subgroup.closure_le _ |>.mpr fun s hs => ?_
    exact gens_even s hs
  intro s hs
  exact h hs

theorem mem_D0_iff (s : Perm (Fin 7)) : s ∈ D0 ↔ s ∈ elts := by
  constructor
  · intro hs
    induction hs using Subgroup.closure_induction_left with
    | one => simp [elts]
    | mul_left y hy z _ ih => exact elts_closed y hy z ih
    | inv_mul_cancel y hy z _ ih =>
      have := gens_inv y hy
      rw [this]
      exact elts_closed y hy z ih
  · intro hs
    have h1 : swap (0 : Fin 7) 1 * swap 2 3 ∈ D0 := Subgroup.subset_closure (by simp [gens])
    have h2 : swap (0 : Fin 7) 2 * swap 1 3 ∈ D0 := Subgroup.subset_closure (by simp [gens])
    have h3 : swap (0 : Fin 7) 1 * swap 4 5 ∈ D0 := Subgroup.subset_closure (by simp [gens])
    simp only [elts, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact D0.one_mem
    · exact h1
    · exact h2
    · exact D0.mul_mem h1 h2
    · exact h3
    · exact D0.mul_mem h1 h3
    · exact D0.mul_mem h2 h3
    · exact D0.mul_mem (D0.mul_mem h1 h2) h3

theorem D0_card : Nat.card D0 = 8 := by
  have e : ↥D0 ≃ ↥(elts.toFinset) := Equiv.subtypeEquivRight (fun s => by
    rw [mem_D0_iff, List.mem_toFinset])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup elts_nodup, elts_length]

end M7

end CFSG.Quasithin.ModC
