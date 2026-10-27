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

namespace CFSG.Sporadic.HNOddCore.FiveData

@[expose] def natWords : Array (List Int) :=
  #[[], [], [], [], [], [-1, 2], [-1, 3], [6, -7], [-1, 4], [6, -9], [8, -10], [-1, 5], [6, -12],
    [8, -13], [11, -14]]

@[expose] def natSizes : List Nat := [7, 6, 5, 4, 3]

@[expose] def fiberPairs : List (Nat × Nat) :=
  [(10, 13), (10, 26), (10, 30), (10, 34), (10, 37),
    (13, 10), (13, 26), (13, 30), (13, 34), (13, 37),
    (26, 10), (26, 13), (26, 30), (26, 34), (26, 37),
    (30, 10), (30, 13), (30, 26), (30, 34), (30, 37),
    (34, 10), (34, 13), (34, 26), (34, 30), (34, 37),
    (37, 10), (37, 13), (37, 26), (37, 30), (37, 34)]

@[expose] def pairWords : Array (List Int) :=
  #[[], [2, 4, 1, 1], [1, 3], [4, 3, 1], [2, 1], [2, 4], [3], [3, 2, 1], [1, 1], [4, 4, 1], [3, 3],
    [2, 4, 1], [2, 2, 3], [4], [1, 2], [2, 1, 1], [2, 3], [4, 1], [3, 2], [4, 2, 2], [1], [3, 2, 1,
    1], [2, 2], [4, 1, 1], [4, 3], [4, 1, 2], [3, 1], [2, 1, 3], [2], [2, 2, 1]]

end CFSG.Sporadic.HNOddCore.FiveData
