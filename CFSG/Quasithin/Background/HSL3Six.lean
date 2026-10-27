module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Quasithin.H.SL3Six

open Matrix

@[expose] def mul3 (a b : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  fun i j => a i 0 * b 0 j + a i 1 * b 1 j + a i 2 * b 2 j

theorem mul3_eq (a b : Matrix (Fin 3) (Fin 3) (ZMod 2)) : mul3 a b = a * b := by
  funext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  rfl

theorem pow_six3 : ∀ x : Matrix (Fin 3) (Fin 3) (ZMod 2),
    mul3 (mul3 x (mul3 x x)) (mul3 x (mul3 x x)) = 1 → mul3 x x = 1 ∨ mul3 x (mul3 x x) = 1 := by
  decide +kernel

theorem pow_six (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : x * x * x * (x * x * x) = 1) :
    x * x = 1 ∨ x * x * x = 1 := by
  have h1 := pow_six3 x
  simp only [mul3_eq, ← mul_assoc] at h1
  exact h1 (by simpa [mul_assoc] using h)

theorem eq_one_or_eq_one_of_commute {t g : SpecialLinearGroup (Fin 3) (ZMod 2)} (ht : t ^ 2 = 1)
    (hg : g ^ 3 = 1) (hc : t * g = g * t) : t = 1 ∨ g = 1 := by
  have hcm : Commute t g := hc
  have h6 : (t * g) ^ 6 = 1 := by
    rw [hcm.mul_pow, show (6 : ℕ) = 2 * 3 from rfl, pow_mul, ht, one_pow, one_mul,
      show (2 * 3 : ℕ) = 3 * 2 from rfl, pow_mul, hg, one_pow]
  have hm := pow_six ((t * g : SpecialLinearGroup (Fin 3) (ZMod 2)) :
    Matrix (Fin 3) (Fin 3) (ZMod 2)) (by
      have := congrArg (fun A : SpecialLinearGroup (Fin 3) (ZMod 2) =>
        (A : Matrix (Fin 3) (Fin 3) (ZMod 2))) h6
      simpa [pow_succ, mul_assoc] using this)
  rcases hm with h2 | h3
  · right
    have e : (t * g) ^ 2 = 1 := Subtype.ext (by simpa [pow_succ, mul_assoc] using h2)
    rw [hcm.mul_pow, ht, one_mul] at e
    have : g = g ^ 3 * (g ^ 2)⁻¹ := by group
    rw [this, hg, e]
    simp
  · left
    have e : (t * g) ^ 3 = 1 := Subtype.ext (by simpa [pow_succ, mul_assoc] using h3)
    rw [hcm.mul_pow, hg, mul_one] at e
    have : t = t ^ 3 * (t ^ 2)⁻¹ := by group
    rw [this, e, ht]
    simp

end CFSG.Quasithin.H.SL3Six
