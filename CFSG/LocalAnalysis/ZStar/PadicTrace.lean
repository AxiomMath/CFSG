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
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
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

namespace CFSG

namespace ZStar.PadicTrace

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

private theorem trace_eq_two_pow_mul_trace_pow_mul
    (A B : Matrix ι ι ℤ_[2]) (hAB : A * B + B * A = B) (n : ℕ) :
    Matrix.trace B =
      (2 ^ n : ℤ_[2]) * Matrix.trace (A ^ n * B) := by
  have hstep : ∀ m : ℕ,
      Matrix.trace (A ^ m * B) =
        2 * Matrix.trace (A ^ (m + 1) * B) := by
    intro m
    calc
      Matrix.trace (A ^ m * B) =
          Matrix.trace (A ^ m * (A * B + B * A)) := by rw [hAB]
      _ = Matrix.trace (A ^ m * (A * B)) +
          Matrix.trace (A ^ m * (B * A)) := by
        rw [mul_add, Matrix.trace_add]
      _ = Matrix.trace (A ^ (m + 1) * B) +
          Matrix.trace (A ^ (m + 1) * B) := by
        congr 1
        · rw [← mul_assoc, ← pow_succ]
        · calc
            Matrix.trace (A ^ m * (B * A)) =
                Matrix.trace ((A ^ m * B) * A) := by rw [mul_assoc]
            _ = Matrix.trace (A * (A ^ m * B)) := Matrix.trace_mul_comm _ _
            _ = Matrix.trace ((A * A ^ m) * B) := by rw [mul_assoc]
            _ = Matrix.trace (A ^ (m + 1) * B) := by rw [pow_succ']
      _ = 2 * Matrix.trace (A ^ (m + 1) * B) := by ring
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        Matrix.trace B =
            (2 ^ n : ℤ_[2]) * Matrix.trace (A ^ n * B) := ih
        _ = (2 ^ n : ℤ_[2]) *
            (2 * Matrix.trace (A ^ (n + 1) * B)) := by rw [hstep n]
        _ = (2 ^ (n + 1) : ℤ_[2]) *
            Matrix.trace (A ^ (n + 1) * B) := by
          rw [pow_succ]
          ring

theorem trace_eq_zero_of_mul_add_mul_eq
    (A B : Matrix ι ι ℤ_[2]) (hAB : A * B + B * A = B) :
    Matrix.trace B = 0 := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [trace_eq_two_pow_mul_trace_pow_mul A B hAB n]
  simp only [map_mul, map_pow, map_zero]
  rw [map_ofNat (PadicInt.toZModPow n) 2]
  have hpow : (2 : ZMod (2 ^ n)) ^ n = 0 := by
    calc
      (2 : ZMod (2 ^ n)) ^ n = ((2 ^ n : ℕ) : ZMod (2 ^ n)) :=
        (Nat.cast_pow 2 n).symm
      _ = 0 := ZMod.natCast_self (2 ^ n)
  rw [hpow, zero_mul]

theorem trace_symmetricBlock_mul_swap_eq_zero
    (P Q : Matrix ι ι ℤ_[2])
    (hidem :
      Matrix.fromBlocks P Q Q P * Matrix.fromBlocks P Q Q P =
        Matrix.fromBlocks P Q Q P) :
    Matrix.trace
      (Matrix.fromBlocks P Q Q P *
        Matrix.fromBlocks (0 : Matrix ι ι ℤ_[2]) 1 1 0) = 0 := by
  have hidem' := hidem
  rw [Matrix.fromBlocks_multiply] at hidem'
  have hoff : P * Q + Q * P = Q := by
    refine Matrix.ext fun i j => ?_
    have h := congrArg
      (fun M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℤ_[2] => M (Sum.inl i) (Sum.inr j))
      hidem'
    simpa using h
  have htraceQ : Matrix.trace Q = 0 :=
    trace_eq_zero_of_mul_add_mul_eq P Q hoff
  rw [Matrix.fromBlocks_multiply]
  simp only [mul_zero, mul_one, zero_add, add_zero]
  change (∑ i : ι ⊕ ι, Matrix.fromBlocks Q P P Q i i) = 0
  rw [Fintype.sum_sum_type]
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]
  change Matrix.trace Q + Matrix.trace Q = 0
  rw [htraceQ, zero_add]

end ZStar.PadicTrace

end CFSG
