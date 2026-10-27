module

public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Field
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res6L364

abbrev Lab : Type := Fin 3 × Fin 3 × Fin 3

@[expose] def wM : Matrix (Fin 3) (Fin 3) F4 := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def dM (i j : Fin 3) : Matrix (Fin 3) (Fin 3) F4 :=
  Matrix.diagonal ![1, ω4 ^ (i : ℕ), ω4 ^ (j : ℕ)]

@[expose] def L (y : Lab) : Matrix (Fin 3) (Fin 3) F4 := dM y.1 y.2.1 * wM ^ (y.2.2 : ℕ)

@[expose] def ev (y : Lab) : Fin 3 → Fin 3 := ![0, y.1, y.2.1]

@[expose] def mulLab (y y' : Lab) : Lab × Fin 3 :=
  let m := y.2.2
  let s : Fin 3 → Fin 3 := fun k => ev y k + ev y' (k - m)
  ((s 1 - s 0, s 2 - s 0, m + y'.2.2), s 0)

theorem L_mul (y y' : Lab) :
    L y * L y' = (ω4 ^ ((mulLab y y').2 : ℕ)) • L (mulLab y y').1 := by
  revert y y'
  decide +kernel

theorem det_L (y : Lab) : (L y).det ≠ 0 := by
  revert y
  decide +kernel

theorem L_zero : L (0, 0, 0) = 1 := by decide

theorem exists_L_ne_zero (y : Lab) : ∃ b : Fin 3, L y 0 b ≠ 0 := by
  revert y
  decide +kernel

theorem L_inj (y y' : Lab) (l : F4) (h : L y = l • L y') : y = y' := by
  revert y y' l
  decide +kernel

@[expose] def comm (y y' : Lab) : Prop := (mulLab y y').1 = (mulLab y' y).1

instance (y y' : Lab) : Decidable (comm y y') := inferInstanceAs (Decidable (_ = _))

@[expose] def zLab : Lab := (1, 2, 0)

@[expose] def t1Lab : Lab := (0, 1, 0)

@[expose] def t2Lab : Lab := (1, 0, 0)

@[expose] def wLab (a : Fin 3) : Lab := (0, a, 1)

theorem card_comm : ∀ y₀ : Lab, y₀ ≠ (0, 0, 0) → y₀ ≠ zLab → y₀ ≠ (2, 1, 0) →
    (Finset.univ.filter (comm y₀)).card = 9 := by
  decide

theorem comm_cases : ∀ y₀ : Lab, y₀ ≠ (0, 0, 0) → y₀ ≠ zLab → y₀ ≠ (2, 1, 0) →
    comm y₀ zLab ∧ ((comm y₀ t1Lab ∧ comm y₀ t2Lab) ∨ ∃ a : Fin 3, comm y₀ (wLab a)) := by
  decide

end CFSG.RankThree.PartTwo.Sec4.Res6L364
