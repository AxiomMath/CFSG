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
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Fam
import CFSG.Quasithin.EmptyFaithful.S14110AuxA4

public section

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.B42A57 CFSG.Quasithin Equiv

namespace CertificateChecks.Batch17023

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.B42A57 CFSG.Quasithin Equiv

private theorem chain3_0 :  ∀ i j : Fin 7, 2 ≤ i.val → i < j →
    (i = 2 ∧ j = 3) ∨ [0, 1, 2, 3, i, j].Nodup ∨
      ∃ k l : Fin 7, [0, 1, 2, 3, k, l].Nodup ∧ [0, 1, i, j, k, l].Nodup  := by
  decide +kernel

end CertificateChecks.Batch17023

namespace Certificates

open CertificateChecks

open Equiv in
theorem certificate17023 : ∀ i j : Fin 7, 2 ≤ i.val → i < j →
    (i = 2 ∧ j = 3) ∨ [0, 1, 2, 3, i, j].Nodup ∨
      ∃ k l : Fin 7, [0, 1, 2, 3, k, l].Nodup ∧ [0, 1, i, j, k, l].Nodup := by
  exact @CertificateChecks.Batch17023.chain3_0

end Certificates
