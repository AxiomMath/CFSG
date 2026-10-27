module

public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowSupplements
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCubicDifferences

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem pgroup_fixed_quotient_escape
    (prime : ℕ) (prime_prime : prime.Prime) (actor base kernel : Subgroup GroupType)
    (actor_pgroup : IsPGroup prime actor) (base_pgroup : IsPGroup prime base)
    (normalized : actor ≤ Subgroup.normalizer (base : Set GroupType))
    (kernel_normal : (kernel.subgroupOf base).Normal)
    (kernel_normalized : actor ≤ Subgroup.normalizer (kernel : Set GroupType))
    (proper : kernel < base) :
    ∃ element ∈ base, element ∉ kernel ∧ ∀ actorElement : actor,
      conjugationDifference actorElement.val element ∈ kernel := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let internalKernel := kernel.subgroupOf base
  let _normal : internalKernel.Normal := kernel_normal
  let _action := conjugationAction actor base normalized
  have invariant := normalized_subgroup_invariant_subgroup actor base kernel normalized kernel_normalized
  let _quotientAction := invariantQuotientAction internalKernel invariant
  have kernel_proper : internalKernel ≠ ⊤ := by
    intro equality
    exact proper.not_ge (Subgroup.subgroupOf_eq_top.mp equality)
  let _nontrivial : Nontrivial (base ⧸ internalKernel) := QuotientGroup.nontrivial_iff.mpr kernel_proper
  have quotient_pgroup := base_pgroup.to_quotient internalKernel
  have divides : prime ∣ Nat.card (base ⧸ internalKernel) := by
    rcases quotient_pgroup.card_eq_or_dvd with cardinality | divides
    · have subsingleton := (Nat.card_eq_one_iff_unique.mp cardinality).1
      exact (not_subsingleton (α := base ⧸ internalKernel) subsingleton).elim
    · exact divides
  have fixed_one : (1 : base ⧸ internalKernel) ∈ MulAction.fixedPoints actor (base ⧸ internalKernel) :=
    fun _ => smul_one _
  obtain ⟨quotientElement, fixed, nonidentity⟩ :=
    actor_pgroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point (base ⧸ internalKernel) divides fixed_one
  obtain ⟨element, projection⟩ := QuotientGroup.mk'_surjective internalKernel quotientElement
  refine ⟨element.val, element.property, ?_, ?_⟩
  · intro kernel_member
    have identity := (QuotientGroup.eq_one_iff element).mpr (show element ∈ internalKernel from kernel_member)
    exact nonidentity (projection.symm.trans identity).symm
  · intro actorElement
    have equality : QuotientGroup.mk' internalKernel (actorElement • element) =
        QuotientGroup.mk' internalKernel element := by
      rw [invariant_quotient_equivariant internalKernel invariant, projection]
      exact fixed actorElement
    have difference := QuotientGroup.eq.mp equality.symm
    change element.val⁻¹ * (actorElement.val * element.val * actorElement.val⁻¹) ∈ kernel at difference
    simpa only [conjugationDifference, mul_assoc] using difference

end CFSG.SignalizerFunctor.Helpers
