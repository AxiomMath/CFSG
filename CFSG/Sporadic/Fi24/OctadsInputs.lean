module

public import CFSG.Sporadic.Fi24.OctadData
public import CFSG.Fischer.NoF25.Steiner
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

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native CFSG.Perm CFSG.Perm.Native CFSG.Fischer

@[expose] def toFin24 (n : ℕ) : Fin 24 := ⟨n % 24, Nat.mod_lt _ (by norm_num)⟩

@[expose] def permF (l : Fin 2) (i : Fin 24) : Fin 24 :=
  ⟨(octPerms[l.val]!)[i.val]! % 24, Nat.mod_lt _ (by norm_num)⟩

@[expose] def octF (k : Fin 759) : Finset (Fin 24) :=
  Finset.univ.filter fun i => octMasks[k.val]!.testBit i.val

@[expose] def octParF (k : Fin 759) : Fin 759 := ⟨octPar[k.val]! % 759, Nat.mod_lt _ (by norm_num)⟩

@[expose] def octLabF (k : Fin 759) : Fin 2 := ⟨octLab[k.val]! % 2, Nat.mod_lt _ (by norm_num)⟩

@[expose] def octads : Finset (Finset (Fin 24)) := Finset.univ.image octF

end CFSG.Sporadic.Fi24
