module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedPointLifting
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantActions
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

universe actorUniverse groupUniverse targetUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem eq_top_of_kernel_le_of_map_eq_top
    {GroupType : Type groupUniverse} [Group GroupType]
    {TargetType : Type targetUniverse} [Group TargetType]
    (homomorphism : GroupType →* TargetType) (subgroup : Subgroup GroupType)
    (kernel_le : homomorphism.ker ≤ subgroup)
    (image_whole : subgroup.map homomorphism = ⊤) : subgroup = ⊤ := by
  apply top_unique
  intro element _
  have image_member : homomorphism element ∈ subgroup.map homomorphism := by
    rw [image_whole]
    trivial
  obtain ⟨representative, representative_member, same_image⟩ := image_member
  have difference_kernel : element * representative⁻¹ ∈ homomorphism.ker := by
    change homomorphism (element * representative⁻¹) = 1
    rw [map_mul, map_inv, same_image, mul_inv_cancel]
  have product_member := subgroup.mul_mem (kernel_le difference_kernel) representative_member
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using product_member

theorem cyclic_quotient_generation_of_normal_extension
    (prime : ℕ) (prime_prime : prime.Prime)
    (ActorType : Type actorUniverse) [CommGroup ActorType]
    (actor_pgroup : IsPGroup prime ActorType)
    (GroupType : Type groupUniverse) [Group GroupType]
    [MulDistribMulAction ActorType GroupType]
    (subgroup : Subgroup GroupType) [subgroup.Normal]
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup,
      actorElement • element ∈ subgroup)
    (subgroup_coprime : Nat.Coprime prime (Nat.card subgroup))
    (subgroup_generated :
      let _action := invariantSubgroupAction subgroup invariant
      (⨆ (actorSubgroup : Subgroup ActorType)
          (_ : IsCyclic (ActorType ⧸ actorSubgroup)),
        FixedPoints.subgroup actorSubgroup subgroup) = ⊤)
    (quotient_generated :
      let _action := invariantQuotientAction subgroup invariant
      (⨆ (actorSubgroup : Subgroup ActorType)
          (_ : IsCyclic (ActorType ⧸ actorSubgroup)),
        FixedPoints.subgroup actorSubgroup (GroupType ⧸ subgroup)) = ⊤) :
    (⨆ (actorSubgroup : Subgroup ActorType) (_ : IsCyclic (ActorType ⧸ actorSubgroup)),
      FixedPoints.subgroup actorSubgroup GroupType) = ⊤ := by
  let _subgroupAction := invariantSubgroupAction subgroup invariant
  let _quotientAction := invariantQuotientAction subgroup invariant
  let generated : Subgroup GroupType :=
    ⨆ (actorSubgroup : Subgroup ActorType) (_ : IsCyclic (ActorType ⧸ actorSubgroup)),
      FixedPoints.subgroup actorSubgroup GroupType
  change generated = ⊤
  have subgroup_le : subgroup ≤ generated := by
    rw [← subgroup.subtype_range, MonoidHom.range_eq_map, ← subgroup_generated]
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro actorSubgroup
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro cyclic
    exact (invariant_subgroup_fixed_points_le subgroup invariant actorSubgroup).trans
      (le_iSup_of_le actorSubgroup (le_iSup_of_le cyclic le_rfl))
  let projection := QuotientGroup.mk' subgroup
  have kernel_coprime : Nat.Coprime prime (Nat.card projection.ker) := by
    simpa only [projection, QuotientGroup.ker_mk'] using subgroup_coprime
  have projected_whole : generated.map projection = ⊤ := by
    apply top_unique
    rw [← quotient_generated]
    apply iSup_le
    intro actorSubgroup
    apply iSup_le
    intro cyclic
    have equivariant : ∀ actorElement : actorSubgroup, ∀ element : GroupType,
        projection (actorElement • element) = actorElement • projection element := by
      intro actorElement element
      exact invariant_quotient_equivariant subgroup invariant actorElement.val element
    rw [← fixed_subgroup_map prime prime_prime (actor_pgroup.to_subgroup actorSubgroup)
      projection (QuotientGroup.mk'_surjective subgroup) equivariant kernel_coprime]
    exact Subgroup.map_mono
      (le_iSup_of_le actorSubgroup (le_iSup_of_le cyclic le_rfl))
  have kernel_le : projection.ker ≤ generated := by
    simpa only [projection, QuotientGroup.ker_mk'] using subgroup_le
  exact eq_top_of_kernel_le_of_map_eq_top projection generated kernel_le projected_whole

end CFSG.SignalizerFunctor.Helpers
