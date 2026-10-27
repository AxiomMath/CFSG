module

public import CFSG.Quasithin.AppendixH.H9.H93.S8CentSwap.AltCentralizerSwap
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

namespace CFSG.ASVolI.ChH

open Equiv

theorem altInfCentralizer_swap {τ : Perm (Fin 8)} (hτ : τ.cycleType = {2}) :
    Nonempty (↥(alternatingGroup (Fin 8) ⊓ Subgroup.centralizer ({τ} : Set (Perm (Fin 8)))) ≃*
      Perm (Fin 6)) := by
  obtain ⟨a, b, hab, rfl⟩ := Equiv.Perm.isSwap_iff_cycleType.mpr hτ
  obtain ⟨φ⟩ := nonempty_alternatingInfCentralizer_swap_mulEquiv hab
  have hcard : ∀ a b : Fin 8, a ≠ b → Fintype.card {x : Fin 8 // x ≠ a ∧ x ≠ b} = 6 := by
    decide
  exact ⟨φ.trans (Fintype.equivFinOfCardEq (hcard a b hab)).permCongrHom⟩

end CFSG.ASVolI.ChH
