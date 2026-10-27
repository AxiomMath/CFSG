module

public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.Quasithin

section Klein

variable {G : Type*} [Group G] {a b : G}

theorem klein_h1 (ha : a * a = 1) : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]

theorem klein_h2 (hb : b * b = 1) (hab : a * b = b * a) : b * (a * b) = a := by
  rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]

theorem klein_h3 (ha : a * a = 1) (hab : a * b = b * a) : a * b * a = b := by
  rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul]

theorem klein_h4 (hb : b * b = 1) : a * b * b = a := by rw [mul_assoc, hb, mul_one]

theorem klein_h5 (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    a * b * (a * b) = 1 := by
  rw [← mul_assoc, klein_h3 ha hab, hb]

@[expose] def kleinFour (a b : G) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    Subgroup G where
  carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl)
    · exact Or.inl (one_mul 1)
    · exact Or.inr (Or.inl (one_mul _))
    · exact Or.inr (Or.inr (Or.inl (one_mul _)))
    · exact Or.inr (Or.inr (Or.inr (one_mul _)))
    · exact Or.inr (Or.inl (mul_one _))
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (klein_h1 ha)))
    · exact Or.inr (Or.inr (Or.inl (mul_one _)))
    · exact Or.inr (Or.inr (Or.inr hab.symm))
    · exact Or.inl hb
    · exact Or.inr (Or.inl (klein_h2 hb hab))
    · exact Or.inr (Or.inr (Or.inr (mul_one _)))
    · exact Or.inr (Or.inr (Or.inl (klein_h3 ha hab)))
    · exact Or.inr (Or.inl (klein_h4 hb))
    · exact Or.inl (klein_h5 ha hb hab)
  inv_mem' := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ha))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hb)))
    · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right (klein_h5 ha hb hab))))

variable {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a}

theorem mem_kleinFour {x : G} :
    x ∈ kleinFour a b ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := Iff.rfl

theorem kleinFour_comm : ∀ x ∈ kleinFour a b ha hb hab, ∀ y ∈ kleinFour a b ha hb hab,
    x * y = y * x := by
  have hab' : Commute a b := hab
  have hy : ∀ y ∈ kleinFour a b ha hb hab, Commute a y ∧ Commute b y := by
    rintro y (rfl | rfl | rfl | rfl)
    · exact ⟨Commute.one_right _, Commute.one_right _⟩
    · exact ⟨Commute.refl _, hab'.symm⟩
    · exact ⟨hab', Commute.refl _⟩
    · exact ⟨(Commute.refl a).mul_right hab', hab'.symm.mul_right (Commute.refl b)⟩
  rintro x (rfl | rfl | rfl | rfl) y hy'
  · exact (Commute.one_left y).eq
  · exact (hy y hy').1.eq
  · exact (hy y hy').2.eq
  · exact (Commute.mul_left (hy y hy').1 (hy y hy').2).eq

theorem kleinFour_sq : ∀ x ∈ kleinFour a b ha hb hab, x ^ 2 = 1 := by
  rintro x (rfl | rfl | rfl | rfl)
  · exact one_pow 2
  · rw [pow_two]
    exact ha
  · rw [pow_two]
    exact hb
  · rw [pow_two]
    exact klein_h5 ha hb hab

theorem card_kleinFour (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card (kleinFour a b ha hb hab) = 4 := by
  have hset : ((kleinFour a b ha hb hab : Subgroup G) : Set G) = {1, a, b, a * b} := by
    ext x
    exact mem_kleinFour.trans (by simp)
  have h1 : (1 : G) ≠ a * b := fun h => hne.symm (mul_left_cancel (show a * b = a * a by
    rw [ha]; exact h.symm))
  have h2 : a ≠ a * b := fun h => hb1 (mul_left_cancel (show a * b = a * 1 by
    rw [mul_one]; exact h.symm))
  have h3 : b ≠ a * b := fun h => ha1 (mul_right_cancel (show a * b = 1 * b by
    rw [one_mul]; exact h.symm))
  show Nat.card ((kleinFour a b ha hb hab : Subgroup G) : Set G) = 4
  rw [Nat.card_coe_set_eq, hset, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_pair h3]
  · simp [hne, h2]
  · simp [ha1.symm, hb1.symm, h1]

end Klein

end CFSG.Quasithin
