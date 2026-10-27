module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
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

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem card_fixedField_of_orderOf {K : Type} [Field K] {r n p : ℕ} (hr : r.Prime) (hn : 1 ≤ n)
    (hK : Nat.card K = r ^ n) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    p ∣ n ∧
      Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = r ^ (n / p) := by
  obtain ⟨σ₁, -, -, -, -, hfix⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hr hn hK
  obtain ⟨hdvd, S, hS, hScard⟩ := hfix (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hσ] at hdvd hScard
  refine ⟨hdvd, ?_⟩
  have hSk : S = RingHom.eqLocusField σ.toRingHom (RingHom.id K) := by
    refine SetLike.coe_injective (Set.ext fun c => ?_)
    rw [hS]
    constructor
    · intro hc
      exact hc σ (Subgroup.mem_zpowers σ)
    · intro hc τ hτ
      have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (K ≃+* K) c :=
        Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hc)
      exact MulAction.mem_stabilizer_iff.1 (hle hτ)
  rw [← hSk]
  exact hScard

end CFSG.SignalizerFunctorTheorem.CatalogBridge
