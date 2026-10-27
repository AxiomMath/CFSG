module

public import CFSG.Permutation.UnitaryThreeRecognition.Conj
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G : Type*} [Group G]

@[expose] def pow5 (x : G) (c : ZMod 5) : G := x ^ c.val

theorem pow5_zero (x : G) : pow5 x 0 = 1 := by simp [pow5]

theorem pow5_one (x : G) : pow5 x 1 = x := by
  rw [pow5, show (1 : ZMod 5).val = 1 from rfl, pow_one]

theorem pow5_add {x : G} (hx : x ^ 5 = 1) (c c' : ZMod 5) :
    pow5 x (c + c') = pow5 x c * pow5 x c' := by
  rw [pow5, pow5, pow5, ← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (c.val + c'.val) 5, pow_add, pow_mul, hx, one_pow, mul_one]

theorem pow5_neg {x : G} (hx : x ^ 5 = 1) (c : ZMod 5) : pow5 x (-c) = (pow5 x c)⁻¹ := by
  have h := pow5_add hx (-c) c
  rw [neg_add_cancel, pow5_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem pow5_mul {x : G} (hx : x ^ 5 = 1) (c c' : ZMod 5) :
    pow5 x (c * c') = pow5 (pow5 x c) c' := by
  rw [pow5, pow5, pow5, ← pow_mul, ZMod.val_mul]
  conv_rhs => rw [← Nat.mod_add_div (c.val * c'.val) 5, pow_add, pow_mul, hx, one_pow, mul_one]

theorem pow5_pow_five {x : G} (hx : x ^ 5 = 1) (c : ZMod 5) : (pow5 x c) ^ 5 = 1 := by
  rw [pow5, ← pow_mul, mul_comm, pow_mul, hx, one_pow]

theorem commute_pow5 {x y : G} (h : x * y = y * x) (c c' : ZMod 5) :
    pow5 x c * pow5 y c' = pow5 y c' * pow5 x c :=
  ((Commute.pow_pow h c.val c'.val)).eq

theorem conj_pow5 (g x : G) (c : ZMod 5) : g * pow5 x c * g⁻¹ = pow5 (g * x * g⁻¹) c := by
  rw [pow5, pow5, conj_pow]

@[expose] def coord5 (z₀ v₀ v₁ : G) (m : ZMod 5 × ZMod 5 × ZMod 5) : G :=
  pow5 z₀ m.1 * pow5 v₀ m.2.1 * pow5 v₁ m.2.2

section

variable {z₀ v₀ v₁ : G} (h0 : z₀ ^ 5 = 1) (h1 : v₀ ^ 5 = 1) (h2 : v₁ ^ 5 = 1)
  (c01 : z₀ * v₀ = v₀ * z₀) (c02 : z₀ * v₁ = v₁ * z₀) (c12 : v₀ * v₁ = v₁ * v₀)
include h0 h1 h2 c01 c02 c12

theorem coord5_add (m m' : ZMod 5 × ZMod 5 × ZMod 5) :
    coord5 z₀ v₀ v₁ (m + m') = coord5 z₀ v₀ v₁ m * coord5 z₀ v₀ v₁ m' := by
  simp only [coord5, Prod.fst_add, Prod.snd_add]
  rw [pow5_add h0, pow5_add h1, pow5_add h2]
  have e1 := commute_pow5 c01 m'.1 m.2.1
  have e2 := commute_pow5 c02 m'.1 m.2.2
  have e3 := commute_pow5 c12 m'.2.1 m.2.2
  have e4 := commute_pow5 c02 m'.1 m.2.2
  calc pow5 z₀ m.1 * pow5 z₀ m'.1 * (pow5 v₀ m.2.1 * pow5 v₀ m'.2.1) *
        (pow5 v₁ m.2.2 * pow5 v₁ m'.2.2)
      = pow5 z₀ m.1 * (pow5 z₀ m'.1 * pow5 v₀ m.2.1) * pow5 v₀ m'.2.1 *
          (pow5 v₁ m.2.2 * pow5 v₁ m'.2.2) := by group
    _ = pow5 z₀ m.1 * pow5 v₀ m.2.1 * (pow5 z₀ m'.1 * pow5 v₀ m'.2.1 * pow5 v₁ m.2.2) *
          pow5 v₁ m'.2.2 := by rw [e1]; group
    _ = pow5 z₀ m.1 * pow5 v₀ m.2.1 * (pow5 v₁ m.2.2 * (pow5 z₀ m'.1 * pow5 v₀ m'.2.1)) *
          pow5 v₁ m'.2.2 := by
        congr 2
        calc pow5 z₀ m'.1 * pow5 v₀ m'.2.1 * pow5 v₁ m.2.2
            = pow5 z₀ m'.1 * (pow5 v₀ m'.2.1 * pow5 v₁ m.2.2) := by group
          _ = pow5 z₀ m'.1 * (pow5 v₁ m.2.2 * pow5 v₀ m'.2.1) := by rw [e3]
          _ = (pow5 z₀ m'.1 * pow5 v₁ m.2.2) * pow5 v₀ m'.2.1 := by group
          _ = (pow5 v₁ m.2.2 * pow5 z₀ m'.1) * pow5 v₀ m'.2.1 := by rw [e4]
          _ = pow5 v₁ m.2.2 * (pow5 z₀ m'.1 * pow5 v₀ m'.2.1) := by group
    _ = pow5 z₀ m.1 * pow5 v₀ m.2.1 * pow5 v₁ m.2.2 *
          (pow5 z₀ m'.1 * pow5 v₀ m'.2.1 * pow5 v₁ m'.2.2) := by group

omit h0 h1 h2 c01 c02 c12 in
theorem coord5_zero : coord5 z₀ v₀ v₁ 0 = 1 := by
  simp [coord5, pow5_zero]

theorem coord5_neg (m : ZMod 5 × ZMod 5 × ZMod 5) :
    coord5 z₀ v₀ v₁ (-m) = (coord5 z₀ v₀ v₁ m)⁻¹ := by
  have h := coord5_add h0 h1 h2 c01 c02 c12 (-m) m
  rw [neg_add_cancel, coord5_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

end

end CFSG.UnitaryThreeRecognition
