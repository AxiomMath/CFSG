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
public import Mathlib.GroupTheory.SpecificGroups.Alternating
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

namespace CFSG.Quasithin

namespace Sp4Inf

open Equiv Pointwise

@[expose] def duad : Finset (Fin 6) := {4, 5}

@[expose] def syn : Finset (Finset (Fin 6)) := {{0, 2}, {1, 3}, {4, 5}}

@[expose] def bq1 (x : Perm (Fin 6)) : Bool := decide (x • duad = duad ∧ Perm.sign x = 1)

@[expose] def bq2 (x : Perm (Fin 6)) : Bool := decide (x • syn = syn ∧ Perm.sign x = 1)

@[expose] def bs0 (x : Perm (Fin 6)) : Bool := bq1 x && bq2 x

@[expose] noncomputable def q1 : Subgroup (Perm (Fin 6)) :=
  MulAction.stabilizer (Perm (Fin 6)) duad ⊓ alternatingGroup (Fin 6)

@[expose] noncomputable def q2 : Subgroup (Perm (Fin 6)) :=
  MulAction.stabilizer (Perm (Fin 6)) syn ⊓ alternatingGroup (Fin 6)

@[expose] noncomputable def s0 : Subgroup (Perm (Fin 6)) := q1 ⊓ q2

end Sp4Inf

end CFSG.Quasithin
