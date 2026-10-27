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
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.KFSU5

open Matrix

section Swap

variable {n : ℕ} {K : Type} [Field K]

@[expose] def swapMatrix (K : Type) [Field K] (i j : Fin n) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun r s => if r = Equiv.swap i j s then 1 else 0

theorem swapMatrix_apply (i j r s : Fin n) :
    swapMatrix K i j r s = if r = Equiv.swap i j s then 1 else 0 := rfl

theorem swapMatrix_mul_self (i j : Fin n) : swapMatrix K i j * swapMatrix K i j = 1 := by
  ext r s
  simp only [Matrix.mul_apply, swapMatrix_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (Equiv.swap i j s)]
  · simp [Equiv.swap_apply_self]
  · intro k _ hk
    simp [hk]
  · simp

theorem swapMatrix_transpose (i j : Fin n) : (swapMatrix K i j)ᵀ = swapMatrix K i j := by
  ext r s
  simp only [Matrix.transpose_apply, swapMatrix_apply]
  have : s = Equiv.swap i j r ↔ r = Equiv.swap i j s := by
    constructor
    · intro h; rw [h, Equiv.swap_apply_self]
    · intro h; rw [h, Equiv.swap_apply_self]
  simp only [this]

theorem swapMatrix_map (bar : K →+* K) (i j : Fin n) :
    (swapMatrix K i j).map bar = swapMatrix K i j := by
  ext r s
  simp only [Matrix.map_apply, swapMatrix_apply]
  split_ifs <;> simp

theorem det_swapMatrix [CharP K 2] (i j : Fin n) : (swapMatrix K i j).det = 1 := by
  have h1 : (swapMatrix K i j).det * (swapMatrix K i j).det = 1 := by
    rw [← Matrix.det_mul, swapMatrix_mul_self, Matrix.det_one]
  have h2 : ((swapMatrix K i j).det - 1) ^ 2 = 0 := by
    linear_combination h1 + (1 - (swapMatrix K i j).det) * (CharTwo.two_eq_zero : (2 : K) = 0)
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)

@[expose] def swapUnit (K : Type) [Field K] (i j : Fin n) : GL (Fin n) K :=
  ⟨swapMatrix K i j, swapMatrix K i j, swapMatrix_mul_self i j, swapMatrix_mul_self i j⟩

theorem swapUnit_val (i j : Fin n) :
    ((swapUnit K i j : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = swapMatrix K i j := rfl

theorem swapUnit_sq (i j : Fin n) : swapUnit K i j ^ 2 = 1 := by
  rw [pow_two]
  apply Units.ext
  simp [swapUnit_val, swapMatrix_mul_self]

theorem swapUnit_ne_one {i j : Fin n} (hij : i ≠ j) : swapUnit K i j ≠ 1 := by
  intro h
  have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i j) h
  simp [swapUnit_val, swapMatrix_apply, hij] at this

theorem orderOf_swapUnit {i j : Fin n} (hij : i ≠ j) : orderOf (swapUnit K i j) = 2 :=
  orderOf_eq_prime (swapUnit_sq i j) (swapUnit_ne_one hij)

theorem swapUnit_mul_comm {i j : Fin n} (a : GL (Fin n) K)
    (ha : ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag)
    (hij : ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i =
      ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j j) :
    swapUnit K i j * a = a * swapUnit K i j := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, swapUnit_val]
  ext r s
  have h1 : (swapMatrix K i j * (a : Matrix (Fin n) (Fin n) K)) r s =
      swapMatrix K i j r s * (a : Matrix (Fin n) (Fin n) K) s s := by
    rw [← ha.diagonal_diag, Matrix.mul_diagonal]; simp [Matrix.diag]
  have h2 : ((a : Matrix (Fin n) (Fin n) K) * swapMatrix K i j) r s =
      (a : Matrix (Fin n) (Fin n) K) r r * swapMatrix K i j r s := by
    rw [← ha.diagonal_diag, Matrix.diagonal_mul]; simp [Matrix.diag]
  rw [h1, h2]
  by_cases hr : r = Equiv.swap i j s
  · have hdiag : (a : Matrix (Fin n) (Fin n) K) s s = (a : Matrix (Fin n) (Fin n) K) r r := by
      rw [hr, Equiv.swap_apply_def]
      split_ifs with h3 h4
      · rw [h3]; exact hij
      · rw [h4]; exact hij.symm
      · rfl
    rw [hdiag, mul_comm]
  · simp [swapMatrix_apply, hr]

end Swap

end CFSG.RankThree.PartOne.KFSU5
