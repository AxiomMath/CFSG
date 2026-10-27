module

public import CFSG.LocalAnalysis.SignalizerFunctor.ConjugateIntersections
public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductEscapeInfrastructure
public import CFSG.LocalAnalysis.SignalizerFunctor.RelativeWeakClosure

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem maximal_invariant_relative_weak_closure (prime : ℕ) (prime_prime : prime.Prime)
    (actor parent complement secondActor kernel : Subgroup GroupType)
    (kernel_le : kernel ≤ complement) (complement_le : complement ≤ parent)
    (kernel_pgroup : IsPGroup prime kernel) (kernel_normal : (kernel.subgroupOf complement).Normal)
    (kernel_actor_normalized : actor ≤ Subgroup.normalizer (kernel : Set GroupType))
    (second_le : secondActor ≤ parent) (second_actor_normalized : actor ≤ Subgroup.normalizer (secondActor : Set GroupType))
    (kernel_intersection : kernel ≤ conjugateIntersection secondActor complement) :
    ∃ subgroup : Subgroup GroupType,
      IsPGroup prime subgroup ∧ actor ≤ Subgroup.normalizer (subgroup : Set GroupType) ∧
      secondActor ≤ Subgroup.normalizer (subgroup : Set GroupType) ∧ kernel ≤ subgroup ∧ subgroup ≤ parent ∧
      relativeWeakClosure parent kernel subgroup = subgroup ∧
      (∀ candidate : Subgroup GroupType, IsPGroup prime candidate →
        actor ≤ Subgroup.normalizer (candidate : Set GroupType) →
        secondActor ≤ Subgroup.normalizer (candidate : Set GroupType) → kernel ≤ candidate → candidate ≤ parent →
        relativeWeakClosure parent kernel candidate = candidate → subgroup ≤ candidate → candidate = subgroup) := by
  let intersection := conjugateIntersection secondActor complement
  let core := (primeSetCore (GroupType := intersection) {prime}).map intersection.subtype
  have orbit_core := normal_prime_subgroup_orbit_le_intersection_core prime prime_prime secondActor complement kernel
    kernel_pgroup kernel_intersection kernel_normal kernel_le
  have core_prime : IsPGroup prime core := (prime_core_isPGroup prime prime_prime).map intersection.subtype
  have orbit_prime : IsPGroup prime (normalizedConjugateHull secondActor kernel) := core_prime.to_le orbit_core
  have orbit_actor_normalized : actor ≤ Subgroup.normalizer (normalizedConjugateHull secondActor kernel : Set GroupType) :=
    normalized_conjugate_hull_external_normalized actor secondActor kernel second_actor_normalized kernel_actor_normalized
  have orbit_le : normalizedConjugateHull secondActor kernel ≤ parent :=
    orbit_core.trans ((Subgroup.map_subtype_le _).trans ((conjugate_intersection_le secondActor complement).trans complement_le))
  let property := fun subgroup : Subgroup GroupType =>
    IsPGroup prime subgroup ∧ actor ≤ Subgroup.normalizer (subgroup : Set GroupType) ∧
    secondActor ≤ Subgroup.normalizer (subgroup : Set GroupType) ∧ kernel ≤ subgroup ∧ subgroup ≤ parent ∧
    relativeWeakClosure parent kernel subgroup = subgroup
  have initial : property (normalizedConjugateHull secondActor kernel) :=
    ⟨orbit_prime, orbit_actor_normalized, normalized_conjugate_hull_normalized secondActor kernel,
      subgroup_le_normalized_conjugate_hull secondActor kernel, orbit_le,
      normalized_orbit_relative_weak_closure parent secondActor kernel second_le⟩
  obtain ⟨subgroup, _, maximal⟩ := Finite.exists_le_maximal initial
  refine ⟨subgroup, maximal.prop.1, maximal.prop.2.1, maximal.prop.2.2.1,
    maximal.prop.2.2.2.1, maximal.prop.2.2.2.2.1, maximal.prop.2.2.2.2.2, ?_⟩
  intro candidate candidate_prime actor_normalized second_normalized kernel_candidate candidate_le weak_equal subgroup_le
  exact (maximal.eq_of_le ⟨candidate_prime, actor_normalized, second_normalized, kernel_candidate, candidate_le, weak_equal⟩
    subgroup_le).symm

end CFSG.SignalizerFunctor.Helpers
