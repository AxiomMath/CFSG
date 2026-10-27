module

import CFSG.Quasithin.AppendixH.H9.H92.NonQuad.FullSpanCase
import CFSG.Quasithin.AppendixH.H9.H92.NonQuad.HyperplaneCase
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

open scoped Matrix

namespace CFSG.ASVolI.ChH

theorem card_le_sixteen_of_not_quadratic (E : Subgroup (GL (Fin 5) (ZMod 2)))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1)
    (hnq : ∃ g ∈ E, ∃ h ∈ E, ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) *
      ((h : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) ≠ 0) :
    Nat.card E ≤ 16 := by
  obtain ⟨g, hg, h', hh, hne⟩ := hnq
  have hcov := subOneCover_subOneSpan hcomm hsq
  have hA : ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) ∈ subOneSpan E := hcov.sub_one_mem g hg
  have hB : ((h' : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) ∈ subOneSpan E := hcov.sub_one_mem h' hh
  have hp : NilPair ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1)
      ((h' : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) :=
    ⟨hcov.mul_self _ hA, hcov.mul_self _ hB, hcov.mul_comm _ hA _ hB⟩
  obtain ⟨v, hv⟩ := exists_vec_mulVec_ne_zero hne
  have hv0 : v ≠ 0 := fun hv0 => hv (by rw [hv0, Matrix.mulVec_zero])
  have h3 := three_le_finrank_nilOrbitSpace hcov hp hA hB hv
  have h5 := finrank_nilOrbitSpace_lt_dim hcov hv0
  by_cases h4 : Module.finrank (ZMod 2) (nilOrbitSpace (subOneSpan E) v) = 4
  · exact card_le_sixteen_of_finrank_nilOrbitSpace_eq_four hcov hv0 h4
  · exact card_le_sixteen_of_finrank_nilOrbitSpace_eq_three hcov hsq hg hh hv (by omega)

end CFSG.ASVolI.ChH
