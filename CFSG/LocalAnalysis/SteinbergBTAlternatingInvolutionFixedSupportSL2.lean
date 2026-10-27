module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.SteinbergBT

open Equiv Subgroup

section Perm

variable {Ω : Type*} [DecidableEq Ω]

theorem swap_mul_swap_comm_of_ne {a b c d : Ω} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : swap a b * swap c d = swap c d * swap a b := by
  refine (Perm.Disjoint.commute fun z => ?_).eq
  by_cases hza : z = a
  · subst hza
    exact Or.inr (swap_apply_of_ne_of_ne hac had)
  by_cases hzb : z = b
  · subst hzb
    exact Or.inr (swap_apply_of_ne_of_ne hbc hbd)
  exact Or.inl (swap_apply_of_ne_of_ne hza hzb)

theorem exists_even_orderOf_eq_four_fin_six :
    ∃ g : Perm (Fin 6), g ^ 4 = 1 ∧ g ^ 2 ≠ 1 ∧ Perm.sign g = 1 :=
  ⟨swap 0 1 * swap 0 2 * swap 0 3 * swap 4 5, by decide, by decide, by decide⟩

end Perm

theorem three_le_card_of_ne {G : Type*} [Group G] [Finite G] (H : Subgroup G) {x y : G}
    (hx : x ∈ H) (hy : y ∈ H) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) : 3 ≤ Nat.card H := by
  by_contra h
  rcases (show Nat.card H ≤ 1 ∨ Nat.card H = 2 by omega) with h1 | h2
  · have : Subsingleton H := Finite.card_le_one_iff_subsingleton.1 h1
    exact hx1 (congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : H) 1))
  · obtain ⟨z, -, hz⟩ := (Nat.card_eq_two_iff' (1 : H)).1 h2
    have h1 := hz ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))
    have h2 := hz ⟨y, hy⟩ (fun h => hy1 (congrArg Subtype.val h))
    exact hxy (congrArg Subtype.val (h1.trans h2.symm))

theorem mul_comm_of_conj_eq {G : Type*} [Group G] {g x : G} (h : g * x * g⁻¹ = x) :
    g * x = x * g :=
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [h]

end CFSG.LocalAnalysis.SteinbergBT
