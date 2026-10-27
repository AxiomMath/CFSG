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

universe actorUniverse groupUniverse actionUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem fixed_transporter_exists
    (prime : ℕ) (prime_prime : prime.Prime)
    (ActorType : Type actorUniverse) [Group ActorType]
    (actor_pgroup : IsPGroup prime ActorType)
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType]
    [MulDistribMulAction ActorType GroupType]
    (ActionType : Type actionUniverse)
    [MulAction GroupType ActionType] [MulAction ActorType ActionType]
    (compatible : ∀ actorElement : ActorType, ∀ groupElement : GroupType,
      ∀ element : ActionType,
      actorElement • (groupElement • element) =
        (actorElement • groupElement) • (actorElement • element))
    (coprime : Nat.Coprime prime (Nat.card GroupType))
    (first second : ActionType)
    (first_fixed : ∀ actorElement : ActorType, actorElement • first = first)
    (second_fixed : ∀ actorElement : ActorType, actorElement • second = second)
    (transporter_nonempty : ∃ groupElement : GroupType, groupElement • first = second) :
    ∃ groupElement : GroupType, groupElement • first = second ∧
      ∀ actorElement : ActorType, actorElement • groupElement = groupElement := by
  classical
  let : Fact prime.Prime := ⟨prime_prime⟩
  obtain ⟨representative, maps⟩ := transporter_nonempty
  let transporter : SubMulAction ActorType GroupType :=
    ⟨{groupElement | groupElement • first = second}, by
      intro actorElement groupElement member
      change (actorElement • groupElement) • first = second
      rw [← first_fixed actorElement, ← compatible, member, second_fixed]⟩
  let transporterEquiv : transporter ≃ MulAction.stabilizer GroupType first :=
    { toFun := fun element => ⟨representative⁻¹ * element.val, by
        change (representative⁻¹ * element.val) • first = first
        rw [mul_smul, element.property, ← maps, inv_smul_smul]⟩
      invFun := fun element => ⟨representative * element.val, by
        change (representative * element.val) • first = second
        rw [mul_smul, element.property, maps]⟩
      left_inv := fun element => Subtype.ext (by simp only [← mul_assoc,
        mul_inv_cancel, one_mul])
      right_inv := fun element => Subtype.ext (by simp only [← mul_assoc,
        inv_mul_cancel, one_mul]) }
  have transporter_coprime : Nat.Coprime prime (Nat.card transporter) := by
    rw [Nat.card_congr transporterEquiv]
    exact coprime.of_dvd_right
      (Subgroup.card_subgroup_dvd_card (MulAction.stabilizer GroupType first))
  obtain ⟨element, fixed⟩ := actor_pgroup.nonempty_fixed_point_of_prime_not_dvd_card
    transporter (prime_prime.coprime_iff_not_dvd.mp transporter_coprime)
  refine ⟨element.val, element.property, ?_⟩
  intro actorElement
  exact congrArg (fun internal : transporter => (internal : GroupType)) (fixed actorElement)

end CFSG.SignalizerFunctor.Helpers
