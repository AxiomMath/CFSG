
module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import Certificates.Data.CFSGNative.Th.Core
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

@[expose] public section

namespace CFSG.Sporadic.Th.Max3.AltQuot

open CFSG.Sporadic.Th.Native CFSG.ComponentClassification.PresentationLocal
open scoped commutatorElement

@[expose] def carmIdx (k : ℕ) (h : 2 ≤ k := by omega) (h' : k < 9 := by omega) :
    CarmichaelIndex 9 :=
  ⟨⟨k, h'⟩, h⟩

@[expose] def carmCubeIdx (k : CarmichaelIndex 9) : Fin 512 :=
  ![0, 0, 0, 0, 0, 1, 1, 1, 0] k.1

@[expose] def carmPairIdx (j k : CarmichaelIndex 9) : Fin 512 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 510, 373, 249, 323, 406, 473], ![0, 0, 0, 0, 1, 458, 465, 462, 68],
    ![0, 0, 0, 0, 0, 160, 202, 263, 475], ![0, 0, 0, 0, 0, 0, 1, 1, 386],
    ![0, 0, 0, 0, 0, 0, 0, 74, 490], ![0, 0, 0, 0, 0, 0, 0, 0, 148],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0]] j.1 k.1

end CFSG.Sporadic.Th.Max3.AltQuot
