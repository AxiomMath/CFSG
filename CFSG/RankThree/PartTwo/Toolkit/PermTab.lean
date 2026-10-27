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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Toolkit

@[expose] def perms3 : List (Equiv.Perm (Fin 3)) :=
  [1, Equiv.swap 1 2, Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 1 2,
    Equiv.swap 0 2 * Equiv.swap 2 1, Equiv.swap 0 2]

@[expose] def perms4 : List (Equiv.Perm (Fin 4)) :=
  [1, Equiv.swap 2 3, Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 2 3,
    Equiv.swap 1 3 * Equiv.swap 3 2, Equiv.swap 1 3, Equiv.swap 0 1,
    Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 1 * Equiv.swap 1 2,
    Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3,
    Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 2, Equiv.swap 0 1 * Equiv.swap 1 3,
    Equiv.swap 0 2 * Equiv.swap 2 1, Equiv.swap 0 2 * Equiv.swap 2 3 * Equiv.swap 3 1,
    Equiv.swap 0 2, Equiv.swap 0 2 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 2 * Equiv.swap 2 1 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 3 2 * Equiv.swap 2 1, Equiv.swap 0 3 * Equiv.swap 3 1,
    Equiv.swap 0 3 * Equiv.swap 3 2, Equiv.swap 0 3,
    Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 1 2, Equiv.swap 0 3 * Equiv.swap 1 2]

@[expose] def ptab {n : ℕ} (σ : Equiv.Perm (Fin n)) : List ℕ := List.ofFn fun i => (σ i).val

@[expose] def toP3 (t : List ℕ) : Equiv.Perm (Fin 3) :=
  (perms3.find? fun σ => ptab σ == t).getD 1

@[expose] def toP4 (t : List ℕ) : Equiv.Perm (Fin 4) :=
  (perms4.find? fun σ => ptab σ == t).getD 1

end CFSG.RankThree.PartTwo.Toolkit
