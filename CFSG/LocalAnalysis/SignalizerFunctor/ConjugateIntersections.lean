module

public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import CFSG.LocalAnalysis.SignalizerFunctor.MatsuyamaWeakClosure

public section

universe groupUniverse actorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

def conjugateIntersection (actor target : Subgroup GroupType) : Subgroup GroupType :=
  ⨅ element : actor, conjugateSubgroup element.val target

theorem conjugate_intersection_le (actor target : Subgroup GroupType) : conjugateIntersection actor target ≤ target := by
  have contained : conjugateIntersection actor target ≤ conjugateSubgroup (1 : actor).val target :=
    iInf_le _ (1 : actor)
  simpa only [Subgroup.coe_one, conjugate_subgroup_one] using contained

theorem normalized_subgroup_le_conjugate_intersection (actor target subgroup : Subgroup GroupType)
    (contained : subgroup ≤ target) (normalized : actor ≤ Subgroup.normalizer (subgroup : Set GroupType)) :
    subgroup ≤ conjugateIntersection actor target := by
  apply le_iInf
  intro actorElement element member
  have inverse_member := Subgroup.le_normalizer_iff.mp normalized actorElement.val⁻¹
    (actor.inv_mem actorElement.property) element member
  refine ⟨actorElement.val⁻¹ * element * actorElement.val,
    contained (by simpa only [inv_inv] using inverse_member), ?_⟩
  change actorElement.val * (actorElement.val⁻¹ * element * actorElement.val) * actorElement.val⁻¹ = element
  group

theorem conjugate_intersection_normalized (actor target : Subgroup GroupType) :
    actor ≤ Subgroup.normalizer (conjugateIntersection actor target : Set GroupType) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator conjugator_member element member
  change conjugator * element * conjugator⁻¹ ∈ ⨅ actorElement : actor, conjugateSubgroup actorElement.val target
  apply Subgroup.mem_iInf.mpr
  intro actorElement
  let inverseActor : actor := ⟨conjugator⁻¹ * actorElement.val,
    actor.mul_mem (actor.inv_mem conjugator_member) actorElement.property⟩
  have inverse_member := (iInf_le (fun actorElement : actor => conjugateSubgroup actorElement.val target)
    inverseActor) member
  have image_member := Subgroup.mem_map_of_mem (MulAut.conj conjugator).toMonoidHom inverse_member
  change conjugator * element * conjugator⁻¹ ∈ conjugateSubgroup conjugator
    (conjugateSubgroup (conjugator⁻¹ * actorElement.val) target) at image_member
  rwa [conjugate_subgroup_mul, mul_inv_cancel_left] at image_member

theorem conjugate_intersection_invariant
    {ActorType : Type actorUniverse} [Group ActorType] [MulDistribMulAction ActorType GroupType]
    (actor target : Subgroup GroupType)
    (actor_invariant : ∀ actorElement : ActorType, ∀ element ∈ actor, actorElement • element ∈ actor)
    (target_invariant : ∀ actorElement : ActorType, ∀ element ∈ target, actorElement • element ∈ target) :
    ∀ actorElement : ActorType, ∀ element ∈ conjugateIntersection actor target,
      actorElement • element ∈ conjugateIntersection actor target := by
  intro actorElement element member
  apply Subgroup.mem_iInf.mpr
  intro conjugator
  let preimage : actor := ⟨actorElement⁻¹ • conjugator.val,
    actor_invariant actorElement⁻¹ conjugator.val conjugator.property⟩
  have original_member := (iInf_le (fun original : actor => conjugateSubgroup original.val target) preimage) member
  obtain ⟨representative, representative_member, product⟩ := original_member
  refine ⟨actorElement • representative, target_invariant actorElement representative representative_member, ?_⟩
  change conjugator.val * (actorElement • representative) * conjugator.val⁻¹ = actorElement • element
  rw [← product]
  change conjugator.val * (actorElement • representative) * conjugator.val⁻¹ =
    actorElement • ((actorElement⁻¹ • conjugator.val) * representative * (actorElement⁻¹ • conjugator.val)⁻¹)
  rw [MulDistribMulAction.smul_mul, MulDistribMulAction.smul_mul, smul_inv', smul_inv_smul]

theorem conjugate_intersection_prime_core_normalized [Finite GroupType]
    (primes : Set ℕ) (actor target : Subgroup GroupType) :
    actor ≤ Subgroup.normalizer
      (((primeSetCore (GroupType := conjugateIntersection actor target) primes).map
        (conjugateIntersection actor target).subtype : Subgroup GroupType) : Set GroupType) := by
  let _characteristic := prime_set_core_characteristic (GroupType := conjugateIntersection actor target) primes
  exact characteristic_subgroup_map_normalized actor _ (conjugate_intersection_normalized actor target) _

theorem normal_prime_subgroup_orbit_le_intersection_core [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (actor target subgroup : Subgroup GroupType)
    (pgroup : IsPGroup prime subgroup) (contained : subgroup ≤ conjugateIntersection actor target)
    (normal : (subgroup.subgroupOf target).Normal) (subgroup_target : subgroup ≤ target) :
    normalizedConjugateHull actor subgroup ≤
      (primeSetCore (GroupType := conjugateIntersection actor target) {prime}).map
        (conjugateIntersection actor target).subtype := by
  let intersection := conjugateIntersection actor target
  have normalizes_target : target ≤ Subgroup.normalizer (subgroup : Set GroupType) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer subgroup_target).mp normal
  have normalizes_intersection : intersection ≤ Subgroup.normalizer (subgroup : Set GroupType) :=
    (conjugate_intersection_le actor target).trans normalizes_target
  have internal_normal : (subgroup.subgroupOf intersection).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer contained).mpr normalizes_intersection
  have internal_pgroup : IsPGroup prime (subgroup.subgroupOf intersection) :=
    pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe contained).symm
  have internal_le := prime_set_core_contains {prime} (subgroup.subgroupOf intersection) internal_normal
    ((prime_supported_singleton_iff_pgroup prime prime_prime _).mpr internal_pgroup)
  have subgroup_core := Subgroup.map_mono (f := intersection.subtype) internal_le
  rw [Subgroup.map_subgroupOf_eq_of_le contained] at subgroup_core
  exact normalized_conjugate_hull_le actor subgroup _ subgroup_core
    (conjugate_intersection_prime_core_normalized {prime} actor target)

end CFSG.SignalizerFunctor.Helpers
