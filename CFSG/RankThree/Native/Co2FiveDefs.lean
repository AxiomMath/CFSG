module

public import CFSG.RankThree.Native.Co2FiveArrays
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

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2

@[expose] def co2FiveQ : Subgroup (Equiv.Perm (Fin 2300)) :=
  Subgroup.closure (permsA 2300 co2FiveQGenArrs)

@[expose] def co2FiveLine (j : Fin 31) : Equiv.Perm (Fin 2300) :=
  permOfArr 2300 (co2FiveLineArr j)

@[expose] def co2FiveC0 : Subgroup (Equiv.Perm (Fin 2300)) :=
  Subgroup.closure (permsA 2300 co2FiveC0GenArrs)

@[expose] def co2FiveC1 : Subgroup (Equiv.Perm (Fin 2300)) :=
  Subgroup.closure (permsA 2300 co2FiveC1GenArrs)

@[expose] def co2FiveA : Subgroup (Equiv.Perm (Fin 2300)) :=
  Subgroup.closure (permsA 2300 co2FiveAGenArrs)

@[expose] def co2FiveD : Subgroup (Equiv.Perm (Fin 2300)) := ⁅co2FiveC1, co2FiveC1⁆

@[expose] def co2FiveRecordOf (j : Fin 31) : Fin 2 := if (j : ℕ) = 0 then 0 else 1

@[expose] def co2FiveRepLine (i : Fin 2) : Fin 31 := Fin.castLE (by norm_num) i

@[expose] def co2FiveTransporter (j : Fin 31) : Equiv.Perm (Fin 2300) :=
  permOfArr 2300 (co2FiveHArr j)

end CFSG.RankThree.Native
