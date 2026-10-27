module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.H13.S126KG

open Matrix

@[expose] def alt4 (x : Fin 6 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, x 0, x 1, x 2; x 0, 0, x 3, x 4; x 1, x 3, 0, x 5; x 2, x 4, x 5, 0]

@[expose] def skew4 {R : Type*} [CommRing R] (x : Fin 6 → R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, x 0, x 1, x 2; -x 0, 0, x 3, x 4; -x 1, -x 3, 0, x 5; -x 2, -x 4, -x 5, 0]

@[expose] def pfR {R : Type*} [CommRing R] (x : Fin 6 → R) : R := x 0 * x 5 - x 1 * x 4 + x 2 * x 3

@[expose] def dotR {R : Type*} [CommRing R] (x y : Fin 6 → R) : R :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 + x 4 * y 4 + x 5 * y 5

theorem sq_add_dot_add_pf_skew {R : Type*} [CommRing R] (x y : Fin 6 → R) :
    (skew4 x * skew4 y) * (skew4 x * skew4 y) + dotR x y • (skew4 x * skew4 y) +
      (pfR x * pfR y) • (1 : Matrix (Fin 4) (Fin 4) R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skew4, dotR, pfR] <;> ring

theorem alt4_eq_skew4 (x : Fin 6 → ZMod 2) : alt4 x = skew4 x := by
  have h : ∀ a : ZMod 2, -a = a := by decide
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alt4, skew4]

@[expose] def pf (x : Fin 6 → ZMod 2) : ZMod 2 := x 0 * x 5 + x 1 * x 4 + x 2 * x 3

theorem pfR_eq (x : Fin 6 → ZMod 2) : pfR x = pf x := by
  have h : ∀ a b : ZMod 2, a - b = a + b := by decide
  simp only [pfR, pf, h]

theorem sq_add_dot_add_pf (x y : Fin 6 → ZMod 2) :
    (alt4 x * alt4 y) * (alt4 x * alt4 y) + dotR x y • (alt4 x * alt4 y) +
      (pf x * pf y) • (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 0 := by
  rw [alt4_eq_skew4, alt4_eq_skew4, ← pfR_eq, ← pfR_eq]
  exact sq_add_dot_add_pf_skew x y

theorem exists_ker_chk : ∀ x : Fin 6 → ZMod 2, pf x = 0 →
    ∃ v : Fin 4 → ZMod 2, v ≠ 0 ∧ alt4 x *ᵥ v = 0 := by
  decide +kernel

theorem pf_eq_one_of_injective {x : Fin 6 → ZMod 2}
    (h : ∀ v : Fin 4 → ZMod 2, alt4 x *ᵥ v = 0 → v = 0) : pf x = 1 := by
  have h01 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  refine h01 _ fun h0 => ?_
  obtain ⟨v, hv, hv0⟩ := exists_ker_chk x h0
  exact hv (h v hv0)

@[expose] def gBlk (x y : Fin 6 → ZMod 2) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  fromBlocks (1 + alt4 x * alt4 y) (alt4 x) (alt4 y) 1

@[expose] def dBlk (x y : Fin 6 → ZMod 2) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  fromBlocks (alt4 x * alt4 y) 0 0 (alt4 y * alt4 x)

theorem two_eq_zero_mat {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n (ZMod 2)) :
    A + A = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  generalize A i j = a
  revert a
  decide

section Blocks

abbrev M4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 2)

theorem blk_tl (z : M4) : (1 + z) * (1 + z) + z = z * (1 + z) + 1 := by
  have h := two_eq_zero_mat z
  calc (1 + z) * (1 + z) + z = (z + z) + (z * (1 + z) + 1) := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]; abel
    _ = z * (1 + z) + 1 := by rw [h, zero_add]

theorem blk_tr (a b : M4) : (1 + a * b) * a + a = a * b * a := by
  have h := two_eq_zero_mat a
  calc (1 + a * b) * a + a = (a + a) + a * b * a := by
        simp only [Matrix.add_mul, Matrix.one_mul]; abel
    _ = a * b * a := by rw [h, zero_add]

theorem blk_bl (a b : M4) : b * (1 + a * b) + b = b * a * b := by
  have h := two_eq_zero_mat b
  calc b * (1 + a * b) + b = (b + b) + b * a * b := by
        simp only [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc]; abel
    _ = b * a * b := by rw [h, zero_add]

end Blocks

theorem gBlk_mul_self (x y : Fin 6 → ZMod 2) : gBlk x y * gBlk x y =
    fromBlocks ((1 + alt4 x * alt4 y) * (1 + alt4 x * alt4 y) + alt4 x * alt4 y)
      ((1 + alt4 x * alt4 y) * alt4 x + alt4 x)
      (alt4 y * (1 + alt4 x * alt4 y) + alt4 y) (alt4 y * alt4 x + 1) := by
  rw [gBlk, fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]

theorem dBlk_mul_add_one (x y : Fin 6 → ZMod 2) : dBlk x y * gBlk x y + 1 =
    fromBlocks (alt4 x * alt4 y * (1 + alt4 x * alt4 y) + 1) (alt4 x * alt4 y * alt4 x)
      (alt4 y * alt4 x * alt4 y) (alt4 y * alt4 x + 1) := by
  rw [gBlk, dBlk, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_add]
  simp only [Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]

theorem gBlk_sq (x y : Fin 6 → ZMod 2) : gBlk x y * gBlk x y = dBlk x y * gBlk x y + 1 := by
  rw [gBlk_mul_self, dBlk_mul_add_one, Matrix.fromBlocks_inj]
  refine ⟨blk_tl _, ?_, ?_, rfl⟩
  · rw [blk_tr]
  · rw [blk_bl]

theorem pow_five_of {R : Type*} [Ring R] (h2 : ∀ a : R, a + a = 0) {g d : R}
    (hg : g * g = d * g + 1) (hd : d * d = d + 1) : g ^ 5 = 1 := by
  have h3 : g ^ 3 = d * g + d := by
    calc g ^ 3 = g * g * g := by rw [pow_succ, pow_two]
      _ = (d * g + 1) * g := by rw [hg]
      _ = d * (g * g) + g := by rw [add_mul, one_mul, mul_assoc]
      _ = d * (d * g + 1) + g := by rw [hg]
      _ = (d * d) * g + d + g := by rw [mul_add, mul_one, ← mul_assoc]
      _ = (d + 1) * g + d + g := by rw [hd]
      _ = d * g + d + (g + g) := by rw [add_mul, one_mul]; abel
      _ = d * g + d := by rw [h2, add_zero]
  have h4 : g ^ 4 = g + d := by
    calc g ^ 4 = g ^ 3 * g := pow_succ g 3
      _ = d * (g * g) + d * g := by rw [h3, add_mul, mul_assoc]
      _ = d * (d * g + 1) + d * g := by rw [hg]
      _ = (d * d) * g + d + d * g := by rw [mul_add, mul_one, ← mul_assoc]
      _ = (d + 1) * g + d + d * g := by rw [hd]
      _ = g + d + (d * g + d * g) := by rw [add_mul, one_mul]; abel
      _ = g + d := by rw [h2, add_zero]
  calc g ^ 5 = g ^ 4 * g := pow_succ g 4
    _ = g * g + d * g := by rw [h4, add_mul]
    _ = 1 + (d * g + d * g) := by rw [hg]; abel
    _ = 1 := by rw [h2, add_zero]

theorem pow_six_of {R : Type*} [Ring R] (h2 : ∀ a : R, a + a = 0) {g d : R}
    (hg : g * g = d * g + 1) (hd : d * d = 1) : g ^ 3 = d ∧ g ^ 6 = 1 := by
  have h3 : g ^ 3 = d := by
    calc g ^ 3 = g * g * g := by rw [pow_succ, pow_two]
      _ = (d * g + 1) * g := by rw [hg]
      _ = d * (g * g) + g := by rw [add_mul, one_mul, mul_assoc]
      _ = d * (d * g + 1) + g := by rw [hg]
      _ = (d * d) * g + d + g := by rw [mul_add, mul_one, ← mul_assoc]
      _ = 1 * g + d + g := by rw [hd]
      _ = d + (g + g) := by rw [one_mul]; abel
      _ = d := by rw [h2, add_zero]
  refine ⟨h3, ?_⟩
  calc g ^ 6 = g ^ 3 * g ^ 3 := by rw [← pow_add]
    _ = 1 := by rw [h3, hd]

theorem dotR_comm (x y : Fin 6 → ZMod 2) : dotR x y = dotR y x := by
  simp only [dotR, mul_comm]

theorem sq_eq (x y : Fin 6 → ZMod 2) (hx : pf x = 1) (hy : pf y = 1) :
    (alt4 x * alt4 y) * (alt4 x * alt4 y) = dotR x y • (alt4 x * alt4 y) + 1 := by
  have h := sq_add_dot_add_pf x y
  rw [hx, hy, mul_one, one_smul, add_assoc] at h
  set W := dotR x y • (alt4 x * alt4 y) + 1 with hW
  set S := (alt4 x * alt4 y) * (alt4 x * alt4 y) with hS
  have h2 := two_eq_zero_mat W
  calc S = S + (W + W) := by rw [h2, add_zero]
    _ = (S + W) + W := (add_assoc _ _ _).symm
    _ = W := by rw [h, zero_add]

theorem dBlk_sq (x y : Fin 6 → ZMod 2) (hx : pf x = 1) (hy : pf y = 1) :
    dBlk x y * dBlk x y = dotR x y • dBlk x y + 1 := by
  rw [dBlk, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, smul_zero]
  rw [sq_eq x y hx hy, sq_eq y x hy hx, dotR_comm y x]

theorem gBlk_pow (x y : Fin 6 → ZMod 2) (hx : pf x = 1) (hy : pf y = 1) :
    gBlk x y ^ 5 = 1 ∨ gBlk x y ^ 6 = 1 := by
  have h2 := two_eq_zero_mat (n := Fin 4 ⊕ Fin 4)
  have hd := dBlk_sq x y hx hy
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hc (dotR x y) with h0 | h1
  · rw [h0, zero_smul, zero_add] at hd
    exact Or.inr (pow_six_of h2 (gBlk_sq x y) hd).2
  · rw [h1, one_smul] at hd
    exact Or.inl (pow_five_of h2 (gBlk_sq x y) hd)

@[expose] def vBlk (x : Fin 6 → ZMod 2) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  fromBlocks 1 (alt4 x) 0 1

@[expose] def iBlk (y : Fin 6 → ZMod 2) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  fromBlocks 1 0 (alt4 y) 1

theorem vBlk_mul_iBlk (x y : Fin 6 → ZMod 2) : vBlk x * iBlk y = gBlk x y := by
  rw [vBlk, iBlk, gBlk, fromBlocks_multiply]
  simp

end CFSG.Quasithin.H13.S126KG
