module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G] {P : Subgroup G}

theorem eq_of_mem_of_card_eq_two (hP : Nat.card P = 2) {x y : G} (hx : x ∈ P) (hy : y ∈ P)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have hx1' : (⟨x, hx⟩ : P) ≠ 1 := fun h => hx1 (Subtype.ext_iff.mp h)
  have hy1' : (⟨y, hy⟩ : P) ≠ 1 := fun h => hy1 (Subtype.ext_iff.mp h)
  obtain ⟨z, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : P)).1 hP
  exact congrArg Subtype.val ((huniq _ hx1').trans (huniq _ hy1').symm)

theorem eq_one_or_eq_of_mem_of_card_eq_two (hP : Nat.card P = 2) {a b : G} (ha : a ∈ P)
    (ha1 : a ≠ 1) (hb : b ∈ P) : b = 1 ∨ b = a :=
  or_iff_not_imp_left.2 fun hb1 => eq_of_mem_of_card_eq_two hP hb ha hb1 ha1

theorem orderOf_eq_two_of_mem_of_card_eq_two (hP : Nat.card P = 2) {x : G} (hx : x ∈ P)
    (hx1 : x ≠ 1) : orderOf x = 2 := by
  have hdvd : orderOf x ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hx
  rw [hP] at hdvd
  exact orderOf_eq_prime (orderOf_dvd_iff_pow_eq_one.1 hdvd) hx1

end CFSG.GroupTheory
