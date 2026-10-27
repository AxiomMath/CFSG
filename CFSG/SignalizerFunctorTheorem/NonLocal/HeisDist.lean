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
public import Mathlib.RingTheory.SimpleRing.Principal
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

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocal

theorem hdist_of_pairing {Γ : Type*} [Group Γ] {T : Type*} [Field T] (Z A : Subgroup Γ) {J : Type*}
    (ζ : T → Γ) (hζmul : ∀ t t', ζ (t + t') = ζ t * ζ t') (hζZ : ∀ t, ζ t ∈ Z)
    (hZζ : ∀ z ∈ Z, ∃ t, ζ t = z) (y : (J → T) → Γ) (a : T → J → Γ)
    (haA : ∀ t j, a t j ∈ A) (hcomm : ∀ v t j, ⁅(y v)⁻¹, a t j⁆ = ζ (t * v j))
    {F : Type*} [Field F] (ξ : Γ → F) (hmul : ∀ z ∈ Z, ∀ z' ∈ Z, ξ (z * z') = ξ z * ξ z')
    (hne0 : ∀ z ∈ Z, ξ z ≠ 0) (hnt : ∃ z ∈ Z, ξ z ≠ 1) (v v' : J → T) (hvv : v ≠ v') :
    ∃ a' ∈ A, ξ ⁅(y v)⁻¹, a'⁆ ≠ ξ ⁅(y v')⁻¹, a'⁆ := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ v' j := by
    by_contra h
    push Not at h
    exact hvv (funext h)
  let ψ : T → F := fun t => ξ (ζ t)
  have hψmul : ∀ t t', ψ (t + t') = ψ t * ψ t' := fun t t' => by
    show ξ (ζ (t + t')) = ξ (ζ t) * ξ (ζ t')
    rw [hζmul, hmul _ (hζZ t) _ (hζZ t')]
  have hψne : ∀ t, ψ t ≠ 0 := fun t => hne0 _ (hζZ t)
  have hψ0 : ψ 0 = 1 := by
    have h1 := hψmul 0 0
    rw [add_zero] at h1
    have : ψ 0 * (ψ 0 - 1) = 0 := by rw [mul_sub, mul_one, ← h1, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (hψne 0))
  have hψnt : ∃ t, ψ t ≠ 1 := by
    obtain ⟨z, hz, hz1⟩ := hnt
    obtain ⟨t, rfl⟩ := hZζ z hz
    exact ⟨t, hz1⟩
  by_contra hcon
  push Not at hcon
  have hall : ∀ t : T, ψ (t * (v j - v' j)) = 1 := by
    intro t
    have h1 := hcon (a t j) (haA t j)
    rw [hcomm, hcomm] at h1
    have h2 : ψ (t * v j) = ψ (t * v' j) := h1
    have h3 : t * (v j - v' j) = t * v j + -(t * v' j) := by ring
    rw [h3, hψmul]
    have h4 : ψ (t * v' j) * ψ (-(t * v' j)) = 1 := by
      rw [← hψmul, add_neg_cancel, hψ0]
    rw [h2, h4]
  obtain ⟨c, hc⟩ := hψnt
  apply hc
  have hd : v j - v' j ≠ 0 := sub_ne_zero.mpr hj
  have := hall (c * (v j - v' j)⁻¹)
  rwa [mul_assoc, inv_mul_cancel₀ hd, mul_one] at this

end CFSG.SignalizerFunctorTheorem.NonLocal
