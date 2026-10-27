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

public section

universe groupUniverse quotientUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem surjective_pgroup_sylow_lift
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    {QuotientType : Type quotientUniverse} [Group QuotientType]
    (prime : ℕ) (prime_prime : prime.Prime)
    (homomorphism : GroupType →* QuotientType) (surjective : Function.Surjective homomorphism)
    (pgroup : IsPGroup prime QuotientType) :
    ∃ sylow : Sylow prime GroupType, (sylow : Subgroup GroupType).map homomorphism = ⊤ := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let target : Sylow prime QuotientType := {
    toSubgroup := ⊤
    isPGroup' := pgroup.of_equiv (Subgroup.topEquiv.symm)
    is_maximal' := by intro subgroup _ contains; exact top_unique contains }
  obtain ⟨sylow, image_eq⟩ := Sylow.mapSurjective_surjective surjective prime target
  have groups_eq := congrArg (fun subgroup : Sylow prime QuotientType => (subgroup : Subgroup QuotientType)) image_eq
  refine ⟨sylow, ?_⟩
  simpa only [Sylow.coe_mapSurjective, target] using groups_eq

theorem surjective_pgroup_element_lift
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    {QuotientType : Type quotientUniverse} [Group QuotientType]
    (prime : ℕ) (prime_prime : prime.Prime)
    (homomorphism : GroupType →* QuotientType) (surjective : Function.Surjective homomorphism)
    (pgroup : IsPGroup prime QuotientType) (element : QuotientType) :
    ∃ lift : GroupType, homomorphism lift = element ∧ ∃ exponent : ℕ, lift ^ (prime ^ exponent) = 1 := by
  obtain ⟨sylow, image_top⟩ := surjective_pgroup_sylow_lift prime prime_prime homomorphism surjective pgroup
  obtain ⟨lift, lift_member, lift_eq⟩ := show element ∈ (sylow : Subgroup GroupType).map homomorphism from
    by rw [image_top]; exact Subgroup.mem_top element
  obtain ⟨exponent, power⟩ := sylow.isPGroup' ⟨lift, lift_member⟩
  exact ⟨lift, lift_eq, exponent, congrArg Subtype.val power⟩

end CFSG.SignalizerFunctor.Helpers
