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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem fixed_product_decomposition
    (prime : ℕ) (prime_prime : prime.Prime)
    (ActorType : Type actorUniverse) [Group ActorType]
    (actor_pgroup : IsPGroup prime ActorType)
    (GroupType : Type groupUniverse) [Group GroupType]
    [MulDistribMulAction ActorType GroupType]
    (first second : Subgroup GroupType)
    (first_invariant : ∀ actorElement : ActorType, ∀ element ∈ first,
      actorElement • element ∈ first)
    (second_invariant : ∀ actorElement : ActorType, ∀ element ∈ second,
      actorElement • element ∈ second)
    (intersection_coprime : Nat.Coprime prime (Nat.card (first ⊓ second : Subgroup GroupType)))
    (element : GroupType) (fixed : ∀ actorElement : ActorType, actorElement • element = element)
    (decomposable : ∃ firstElement ∈ first, ∃ secondElement ∈ second,
      firstElement * secondElement = element) :
    ∃ firstElement ∈ first, ∃ secondElement ∈ second,
      firstElement * secondElement = element ∧
      (∀ actorElement : ActorType, actorElement • firstElement = firstElement) ∧
      (∀ actorElement : ActorType, actorElement • secondElement = secondElement) := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  obtain ⟨firstRepresentative, first_member, secondRepresentative, second_member, product⟩ :=
    decomposable
  let fibre : SubMulAction ActorType (GroupType × GroupType) :=
    ⟨{pair | pair.1 ∈ first ∧ pair.2 ∈ second ∧ pair.1 * pair.2 = element}, by
      intro actorElement pair member
      refine ⟨first_invariant actorElement pair.1 member.1,
        second_invariant actorElement pair.2 member.2.1, ?_⟩
      change (actorElement • pair.1) * (actorElement • pair.2) = element
      rw [← MulDistribMulAction.smul_mul, member.2.2, fixed]⟩
  let fibreEquiv : fibre ≃ (first ⊓ second : Subgroup GroupType) :=
    { toFun := fun pair => ⟨firstRepresentative⁻¹ * pair.val.1, by
        refine ⟨first.mul_mem (first.inv_mem first_member) pair.property.1, ?_⟩
        have difference : firstRepresentative⁻¹ * pair.val.1 =
            secondRepresentative * pair.val.2⁻¹ := by
          apply (eq_mul_inv_iff_mul_eq).mpr
          rw [mul_assoc, pair.property.2.2, ← product]
          simp only [← mul_assoc, inv_mul_cancel, one_mul]
        rw [difference]
        exact second.mul_mem second_member (second.inv_mem pair.property.2.1)⟩
      invFun := fun internal => ⟨(firstRepresentative * internal.val,
        internal.val⁻¹ * secondRepresentative), by
          refine ⟨first.mul_mem first_member internal.property.1,
            second.mul_mem (second.inv_mem internal.property.2) second_member, ?_⟩
          simpa only [mul_assoc, mul_inv_cancel_left] using product⟩
      left_inv := fun pair => by
        apply Subtype.ext
        apply Prod.ext
        · simp only [mul_inv_cancel_left]
        · change (firstRepresentative⁻¹ * pair.val.1)⁻¹ * secondRepresentative = pair.val.2
          rw [mul_inv_rev, inv_inv, mul_assoc, product, ← pair.property.2.2]
          simp only [inv_mul_cancel_left]
      right_inv := fun internal => by
        apply Subtype.ext
        exact inv_mul_cancel_left firstRepresentative internal.val }
  have fibre_coprime : Nat.Coprime prime (Nat.card fibre) := by
    rw [Nat.card_congr fibreEquiv]
    exact intersection_coprime
  obtain ⟨pair, pair_fixed⟩ := actor_pgroup.nonempty_fixed_point_of_prime_not_dvd_card fibre
    (prime_prime.coprime_iff_not_dvd.mp fibre_coprime)
  refine ⟨pair.val.1, pair.property.1, pair.val.2, pair.property.2.1,
    pair.property.2.2, ?_, ?_⟩
  · intro actorElement
    exact congrArg (fun internal : fibre => internal.val.1) (pair_fixed actorElement)
  · intro actorElement
    exact congrArg (fun internal : fibre => internal.val.2) (pair_fixed actorElement)

end CFSG.SignalizerFunctor.Helpers
