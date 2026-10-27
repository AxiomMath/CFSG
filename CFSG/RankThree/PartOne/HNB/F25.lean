module

public import Certificates.Data.HNUnitaryBridge
public import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

namespace CFSG.RankThree.PartOne.HNB

open HNUnitaryBridge

@[expose] def F25 : Type := ZMod 5 × ZMod 5

namespace F25

instance : DecidableEq F25 := inferInstanceAs (DecidableEq (ZMod 5 × ZMod 5))

instance : Fintype F25 := inferInstanceAs (Fintype (ZMod 5 × ZMod 5))

instance : Zero F25 := ⟨((0 : ZMod 5), (0 : ZMod 5))⟩

instance : One F25 := ⟨((1 : ZMod 5), (0 : ZMod 5))⟩

instance : Add F25 := ⟨fun x y => (x.1 + y.1, x.2 + y.2)⟩

instance : Neg F25 := ⟨fun x => (-x.1, -x.2)⟩

instance : Mul F25 := ⟨fun x y => (x.1 * y.1 + 2 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)⟩

@[expose] def norm (x : F25) : ZMod 5 := x.1 * x.1 - 2 * x.2 * x.2

instance : Inv F25 := ⟨fun x => ((norm x)⁻¹ * x.1, -((norm x)⁻¹ * x.2))⟩

instance : Field F25 :=
  Field.ofMinimalAxioms F25 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

instance : Finite F25 := inferInstance

theorem card : Nat.card F25 = 25 := by
  rw [Nat.card_eq_fintype_card]
  rfl

end F25

@[expose] def dec (n : ℕ) : F25 := (((n % 5 : ℕ) : ZMod 5), ((n / 5 % 5 : ℕ) : ZMod 5))

theorem dec_mod (n : ℕ) : dec n = dec (n % 25) := by
  have h1 : n % 5 = n % 25 % 5 := by omega
  have h2 : n / 5 % 5 = n % 25 / 5 % 5 := by omega
  unfold dec
  rw [← h1, ← h2]

theorem dec_fadd (x y : ℕ) : dec (fadd x y) = dec x + dec y := by
  have key : ∀ x < 25, ∀ y < 25, dec (fadd x y) = dec x + dec y := by decide +kernel
  have hx : fadd x y = fadd (x % 25) (y % 25) := by
    have h1 : x % 5 = x % 25 % 5 := by omega
    have h2 : x / 5 % 5 = x % 25 / 5 % 5 := by omega
    have h3 : y % 5 = y % 25 % 5 := by omega
    have h4 : y / 5 % 5 = y % 25 / 5 % 5 := by omega
    unfold fadd
    rw [← h1, ← h2, ← h3, ← h4]
  rw [hx, dec_mod x, dec_mod y]
  exact key _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))

theorem dec_fmul (x y : ℕ) : dec (fmul x y) = dec x * dec y := by
  have key : ∀ x < 25, ∀ y < 25, dec (fmul x y) = dec x * dec y := by decide +kernel
  have hx : fmul x y = fmul (x % 25) (y % 25) := by
    have h1 : x % 5 = x % 25 % 5 := by omega
    have h2 : x / 5 % 5 = x % 25 / 5 % 5 := by omega
    have h3 : y % 5 = y % 25 % 5 := by omega
    have h4 : y / 5 % 5 = y % 25 / 5 % 5 := by omega
    unfold fmul
    rw [← h1, ← h2, ← h3, ← h4]
  rw [hx, dec_mod x, dec_mod y]
  exact key _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))

theorem dec_injOn : ∀ x < 25, ∀ y < 25, dec x = dec y → x = y := by decide +kernel

theorem dec_zero : dec 0 = 0 := rfl

theorem dec_one : dec 1 = 1 := rfl

@[expose] def decMat (f : ℕ → ℕ) : Matrix (Fin 3) (Fin 3) F25 :=
  Matrix.of fun r s => dec (f (3 * r + s))

theorem decMat_mprod (A B : ℕ → ℕ) : decMat (mprod A B) = decMat A * decMat B := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [decMat, mprod, Matrix.mul_apply, Fin.sum_univ_three, dec_fadd, dec_fmul]

end CFSG.RankThree.PartOne.HNB
