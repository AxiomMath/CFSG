module

public import CFSG.OddTranspositions.PartThree.Eleven.Five.Refl
public import CFSG.OddTranspositions.PartThree.FiveReflectionFischer

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

theorem fiveForm_add_right (n : ℕ) (ε : Bool) (x y z : Fin (n + 1) → ZMod 5) :
    fiveForm n ε x (y + z) = fiveForm n ε x y + fiveForm n ε x z := by
  simp only [fiveForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem fiveForm_neg_right (n : ℕ) (ε : Bool) (x y : Fin (n + 1) → ZMod 5) :
    fiveForm n ε x (-y) = -fiveForm n ε x y := by
  simp only [fiveForm, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  ring

theorem fiveForm_neg_left (n : ℕ) (ε : Bool) (x y : Fin (n + 1) → ZMod 5) :
    fiveForm n ε (-x) y = -fiveForm n ε x y := by
  simp only [fiveForm, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  ring

theorem fiveForm_sub_left (n : ℕ) (ε : Bool) (x y z : Fin (n + 1) → ZMod 5) :
    fiveForm n ε (x - y) z = fiveForm n ε x z - fiveForm n ε y z := by
  rw [sub_eq_add_neg, fiveForm_add_left, fiveForm_neg_left, sub_eq_add_neg]

theorem fiveForm_sub_right (n : ℕ) (ε : Bool) (x y z : Fin (n + 1) → ZMod 5) :
    fiveForm n ε x (y - z) = fiveForm n ε x y - fiveForm n ε x z := by
  rw [sub_eq_add_neg, fiveForm_add_right, fiveForm_neg_right, sub_eq_add_neg]

theorem fiveForm_smul_right (n : ℕ) (ε : Bool) (c : ZMod 5)
    (x y : Fin (n + 1) → ZMod 5) :
    fiveForm n ε x (c • y) = c * fiveForm n ε x y := by
  rw [fiveForm_comm, fiveForm_smul_left, fiveForm_comm]

namespace FiveAux

abbrev V5 := Fin 5 → ZMod 5

theorem fiveQ_smul (c : ZMod 5) (x : V5) :
    fiveForm 4 true (c • x) (c • x) = c ^ 2 * fiveForm 4 true x x := by
  rw [fiveForm_smul_left, fiveForm_smul_right]
  ring

theorem zmod5_ne_zero_cases (c : ZMod 5) (hc : c ≠ 0) :
    c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
  have h : ∀ c : ZMod 5, c ≠ 0 → c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by decide
  exact h c hc

theorem zmod5_two_mul_eq_zero {a : ZMod 5} (h : (2 : ZMod 5) * a = 0) : a = 0 := by
  have h' : ∀ a : ZMod 5, (2 : ZMod 5) * a = 0 → a = 0 := by decide
  exact h' a h

end FiveAux

end CFSG.OddTranspositions.PartThree
