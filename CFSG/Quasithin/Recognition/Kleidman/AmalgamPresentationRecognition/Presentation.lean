module

public import Certificates.Data.CFSGNative.CosetTable.Enum
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

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

open CFSG.CosetTable

@[expose] def j3WordsRest : List (List (Fin 7 × Bool)) := [
  [(1, true), (1, true)],
  [(3, true), (3, true)],
  [(2, true), (2, true)],
  [(5, true), (5, true)],
  [(0, true), (0, true), (0, true)],
  [(4, true), (3, true), (4, false), (3, true)],
  [(0, true), (2, true), (0, false), (2, true)],
  [(0, true), (1, true), (0, false), (1, true)],
  [(1, true), (3, true), (1, true), (3, true)],
  [(0, false), (5, true), (0, false), (5, true)],
  [(5, true), (3, true), (5, true), (3, true)],
  [(3, true), (2, true), (4, false), (2, true), (4, true)],
  [(5, true), (2, true), (5, true), (3, true), (1, true)],
  [(2, true), (1, true), (2, true), (3, true), (1, true)],
  [(4, true), (0, false), (1, true), (4, true), (0, false), (1, true)],
  [(2, true), (4, false), (4, false), (0, false), (4, false), (4, false), (0, false)],
  [(4, false), (0, false), (4, true), (0, false), (4, false), (1, true), (2, true)],
  [(4, false), (5, true), (4, true), (0, true), (5, true), (4, false), (0, false), (5, true), (1, true), (2, true)],
  [(6, false), (2, true), (0, false), (6, false)],
  [(6, true), (0, true), (6, true), (2, true)],
  [(6, false), (6, false), (0, false), (2, true)],
  [(6, false), (3, true), (6, false), (3, true), (0, false)],
  [(2, true), (1, true), (3, true), (2, true), (1, true)],
  [(6, false), (1, true), (6, false), (1, true), (6, false), (1, true)],
  [(4, true), (4, true), (4, true), (4, true), (4, true), (4, true)],
  [(4, false), (4, false), (0, false), (4, false), (4, false), (6, true), (6, true)],
  [(3, true), (6, true), (4, false), (1, true), (6, false), (4, true), (1, true)],
  [(2, true), (6, true), (2, true), (6, false)],
  [(0, true), (3, true), (0, false), (3, true)],
  [(6, true), (3, true), (0, true), (6, true), (3, true)],
  [(5, true), (2, true), (3, true), (5, true), (1, true)]
]

@[expose] def octWord : List (Fin 7 × Bool) :=
  [(6, false), (5, true), (6, false), (5, true), (6, false), (5, true), (6, true), (5, true), (6, true), (5, true), (6, false), (5, true), (6, false), (5, true), (6, false), (5, true), (2, true), (1, true)]

@[expose] def j3Words : List (List (Fin 7 × Bool)) := j3WordsRest ++ [octWord]

@[expose] def SatisfiesJ3Words {X : Type*} [Group X] (ρ : Fin 7 → X) : Prop :=
  ∀ r ∈ j3Words, FreeGroup.lift ρ (FreeGroup.mk r) = 1

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
