module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType

theorem two_mul_eq_of_secondDiff {p : ℕ} (w : ZMod p → ZMod p) (C : ZMod p)
    (h : ∀ j, w (j + 2) - 2 * w (j + 1) + w j = C) (k : ℕ) :
    2 * w k = 2 * w 0 + 2 * (k : ZMod p) * (w 1 - w 0) +
      C * (k : ZMod p) * ((k : ZMod p) - 1) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp
    | 1 => simp only [Nat.cast_one, sub_self, mul_zero, add_zero]; ring
    | k + 2 =>
      have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      have hk := h (k : ZMod p)
      push_cast at h1 h0 ⊢
      have hrec : w ((k : ZMod p) + 2) = 2 * w ((k : ZMod p) + 1) - w (k : ZMod p) + C := by
        linear_combination hk
      rw [hrec]
      linear_combination 2 * h1 - h0

theorem two_ne_zero_zmod {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')

theorem eq_zero_of_secondDiff {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (w : ZMod p → ZMod p)
    (C : ZMod p) (h : ∀ j, w (j + 2) - 2 * w (j + 1) + w j = C) {j₁ j₂ j₃ : ZMod p}
    (h12 : j₁ ≠ j₂) (h13 : j₁ ≠ j₃) (h23 : j₂ ≠ j₃) (he2 : w j₁ = w j₂) (he3 : w j₁ = w j₃) :
    ∀ j, w j = w 0 := by
  have key : ∀ j : ZMod p, 2 * w j = 2 * w 0 + 2 * j * (w 1 - w 0) + C * j * (j - 1) := by
    intro j
    have := two_mul_eq_of_secondDiff w C h j.val
    rwa [ZMod.natCast_zmod_val] at this
  have h2 := two_ne_zero_zmod (p := p) hp2
  have e12 : (j₁ - j₂) * (2 * (w 1 - w 0) + C * (j₁ + j₂ - 1)) = 0 := by
    linear_combination (key j₂) - (key j₁) + 2 * he2
  have e13 : (j₁ - j₃) * (2 * (w 1 - w 0) + C * (j₁ + j₃ - 1)) = 0 := by
    linear_combination (key j₃) - (key j₁) + 2 * he3
  have f12 := (mul_eq_zero.mp e12).resolve_left (sub_ne_zero.mpr h12)
  have f13 := (mul_eq_zero.mp e13).resolve_left (sub_ne_zero.mpr h13)
  have hC : C * (j₂ - j₃) = 0 := by linear_combination f12 - f13
  have hC0 : C = 0 := (mul_eq_zero.mp hC).resolve_right (sub_ne_zero.mpr h23)
  have hD : 2 * (w 1 - w 0) = 0 := by
    have := f12
    rw [hC0, zero_mul, add_zero] at this
    exact this
  intro j
  have hj := key j
  rw [hC0, mul_assoc 2 j, mul_comm j, ← mul_assoc, hD] at hj
  have : 2 * (w j - w 0) = 0 := by linear_combination hj
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)

end CFSG.StandardType
