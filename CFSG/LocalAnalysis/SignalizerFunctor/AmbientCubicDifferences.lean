module

public import CFSG.LocalAnalysis.SignalizerFunctor.Coprime
public import CFSG.LocalAnalysis.SignalizerFunctor.OddPGroupCubicDifferences

public section

open scoped commutatorElement

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

@[expose] def conjugationDifference (actorElement element : GroupType) : GroupType :=
  element⁻¹ * actorElement * element * actorElement⁻¹

theorem ambient_class_two_cubic_differences_abelian
    (prime : ℕ) (prime_prime : prime.Prime) (odd_prime : prime ≠ 2)
    (actor base : Subgroup GroupType) (pgroup : IsPGroup prime base)
    (abelian : IsMulCommutative actor)
    (normalized : actor ≤ Subgroup.normalizer (base : Set GroupType))
    (class_two : ⁅base, base⁆ ≤ Subgroup.centralizer (base : Set GroupType))
    (fixed_derived : actor ≤ Subgroup.centralizer ((⁅base, base⁆ : Subgroup GroupType) : Set GroupType))
    (element : GroupType) (member : element ∈ base)
    (cubic : ∀ first second third : actor,
      conjugationDifference third.val
        (conjugationDifference second.val (conjugationDifference first.val element)) = 1) :
    IsMulCommutative (Subgroup.closure (Set.range (fun actorElement : actor =>
      conjugationDifference actorElement.val element))) := by
  let := abelian
  let _action := conjugationAction actor base normalized
  have action_formula : ∀ actorElement : actor, ∀ value : base,
      (actorElement • value : base).val = actorElement.val * value.val * actorElement.val⁻¹ :=
    fun _ _ => rfl
  have internal_class_two : ∀ first second : base, ⁅first, second⁆ ∈ Subgroup.center base := by
    intro first second
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp
      (class_two (Subgroup.commutator_mem_commutator first.property second.property)) other.val other.property
  have internal_fixed : ∀ actorElement : actor, ∀ first second : base,
      actorElement • ⁅first, second⁆ = ⁅first, second⁆ := by
    intro actorElement first second
    apply Subtype.ext
    change actorElement.val * ⁅first.val, second.val⁆ * actorElement.val⁻¹ = ⁅first.val, second.val⁆
    have commutes := Subgroup.mem_centralizer_iff.mp (fixed_derived actorElement.property)
      ⁅first.val, second.val⁆ (Subgroup.commutator_mem_commutator first.property second.property)
    rw [← commutes, mul_assoc, mul_inv_cancel, mul_one]
  let internalElement : base := ⟨element, member⟩
  have internal_cubic : ∀ first second third : actor,
      third • ((internalElement⁻¹ * (first • internalElement))⁻¹ *
        (second • (internalElement⁻¹ * (first • internalElement)))) =
      (internalElement⁻¹ * (first • internalElement))⁻¹ *
        (second • (internalElement⁻¹ * (first • internalElement))) := by
    intro first second third
    apply Subtype.ext
    have equality := cubic first second third
    unfold conjugationDifference at equality
    apply Eq.symm
    apply inv_mul_eq_one.mp
    simpa only [action_formula, Subgroup.coe_mul, Subgroup.coe_inv, internalElement, mul_assoc] using equality
  apply CFSG.subgroup_isMulCommutative_closure
  rintro _ ⟨firstActor, rfl⟩ _ ⟨secondActor, rfl⟩
  have commutes := class_two_odd_pgroup_cubic_differences_commute prime prime_prime odd_prime pgroup
    internal_class_two actor internal_fixed internalElement internal_cubic firstActor secondActor
  simpa only [conjugationDifference, action_formula, Subgroup.coe_mul, Subgroup.coe_inv, internalElement, mul_assoc]
    using congrArg Subtype.val commutes.eq

end CFSG.SignalizerFunctor.Helpers
