module

public import CFSG.Certificates.NativeRefine
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

namespace CFSG.Sporadic.Co2Smith

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def ArcComm (σ : Equiv.Perm (Fin 2300)) (p : Array ℕ) : Prop :=
  p.size = 2300 ∧ ∃ A : Equiv.Perm (Fin 2300), Rep 2300 p A ∧ σ * A = A * σ

variable {σ : Equiv.Perm (Fin 2300)}

theorem ArcComm.apply {p : Array ℕ} (h : ArcComm σ p) {A : Equiv.Perm (Fin 2300)}
    (hA : Rep 2300 p A) (x : Fin 2300) :
    p[((σ x : Fin 2300) : ℕ)]! = ((σ (A x) : Fin 2300) : ℕ) := by
  obtain ⟨-, B, hB, hc⟩ := h
  rw [hB.unique hA] at hc
  rw [hA (σ x), ← Equiv.Perm.mul_apply, ← hc, Equiv.Perm.mul_apply]

variable {nbr : Array (List ℕ)} (hnbr : ∀ x : Fin 2300, PointList 2300 nbr[(x : ℕ)]!)
  (hσ : NbrInv nbr σ)
include hnbr hσ

end CFSG.Sporadic.Co2Smith
