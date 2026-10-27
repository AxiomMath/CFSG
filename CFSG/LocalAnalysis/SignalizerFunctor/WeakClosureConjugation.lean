module

public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowSupplements
public import CFSG.LocalAnalysis.SignalizerFunctor.RelativeWeakClosure

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem relative_weak_closure_conjugate_le (parent target bound : Subgroup GroupType)
    (element : GroupType) (element_member : element ∈ parent) :
    conjugateSubgroup element (relativeWeakClosure parent target bound) ≤
      relativeWeakClosure parent target (conjugateSubgroup element bound) := by
  change (relativeWeakClosure parent target bound).map (MulAut.conj element).toMonoidHom ≤ _
  unfold relativeWeakClosure
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro original
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro contained
  change conjugateSubgroup element (conjugateSubgroup original.val target) ≤ _
  rw [conjugate_subgroup_mul]
  have new_contained : conjugateSubgroup (element * original.val) target ≤ conjugateSubgroup element bound := by
    rw [← conjugate_subgroup_mul]
    exact Subgroup.map_mono contained
  exact le_iSup_of_le (⟨element * original.val, parent.mul_mem element_member original.property⟩ : parent)
    (le_iSup_of_le new_contained le_rfl)

theorem relative_weak_closure_conjugate (parent target bound : Subgroup GroupType)
    (element : GroupType) (element_member : element ∈ parent) :
    conjugateSubgroup element (relativeWeakClosure parent target bound) =
      relativeWeakClosure parent target (conjugateSubgroup element bound) := by
  apply le_antisymm (relative_weak_closure_conjugate_le parent target bound element element_member)
  have inverse := relative_weak_closure_conjugate_le parent target (conjugateSubgroup element bound) element⁻¹
    (parent.inv_mem element_member)
  rw [conjugate_subgroup_inv_cancel] at inverse
  have mapped := Subgroup.map_mono (f := (MulAut.conj element).toMonoidHom) inverse
  change conjugateSubgroup element (conjugateSubgroup element⁻¹
      (relativeWeakClosure parent target (conjugateSubgroup element bound))) ≤
    conjugateSubgroup element (relativeWeakClosure parent target bound) at mapped
  rwa [conjugate_subgroup_mul, mul_inv_cancel, conjugate_subgroup_one] at mapped

theorem conjugate_subgroup_normalizes (actor target : Subgroup GroupType) (element : GroupType)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    conjugateSubgroup element actor ≤ Subgroup.normalizer (conjugateSubgroup element target : Set GroupType) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator conjugator_member value member
  obtain ⟨originalConjugator, originalConjugator_member, conjugator_equal⟩ := conjugator_member
  obtain ⟨original, original_member, value_equal⟩ := member
  have original_normalized := Subgroup.le_normalizer_iff.mp normalized originalConjugator originalConjugator_member
    original original_member
  refine ⟨originalConjugator * original * originalConjugator⁻¹, original_normalized, ?_⟩
  change element * (originalConjugator * original * originalConjugator⁻¹) * element⁻¹ = conjugator * value * conjugator⁻¹
  change element * originalConjugator * element⁻¹ = conjugator at conjugator_equal
  change element * original * element⁻¹ = value at value_equal
  rw [← conjugator_equal, ← value_equal]
  group

variable [Finite GroupType]

theorem normalized_sylows_conjugate_by_common_fixed (prime sylowPrime : ℕ)
    (prime_prime : prime.Prime) (sylowPrime_prime : sylowPrime.Prime)
    (actor parent : Subgroup GroupType) (actor_pgroup : IsPGroup prime actor)
    (normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card parent)) (first second : Sylow sylowPrime parent)
    (first_normalized : actor ≤ Subgroup.normalizer
      (((first : Subgroup parent).map parent.subtype : Subgroup GroupType) : Set GroupType))
    (second_normalized : actor ≤ Subgroup.normalizer
      (((second : Subgroup parent).map parent.subtype : Subgroup GroupType) : Set GroupType)) :
    ∃ element ∈ parent ⊓ Subgroup.centralizer (actor : Set GroupType),
      conjugateSubgroup element ((first : Subgroup parent).map parent.subtype) =
        (second : Subgroup parent).map parent.subtype := by
  let _action := conjugationAction actor parent normalized
  obtain ⟨element, conjugates, fixed⟩ := invariant_sylows_conjugate_by_fixed_element prime sylowPrime prime_prime
    sylowPrime_prime actor actor_pgroup parent coprime first second
    (invariant_subgroup_sylow_fixed actor parent normalized sylowPrime first first_normalized)
    (invariant_subgroup_sylow_fixed actor parent normalized sylowPrime second second_normalized)
  have subgroup_equal : conjugateSubgroup element (first : Subgroup parent) = second :=
    congrArg (fun sylow : Sylow sylowPrime parent => (sylow : Subgroup parent)) conjugates
  refine ⟨element.val, ⟨element.property, ?_⟩, ?_⟩
  · apply Subgroup.mem_centralizer_iff.mpr
    intro actorElement member
    have equality := congrArg Subtype.val (fixed ⟨actorElement, member⟩)
    change actorElement * element.val * actorElement⁻¹ = element.val at equality
    exact (mul_inv_eq_iff_eq_mul).mp equality
  · have mapped := congrArg (Subgroup.map parent.subtype) subgroup_equal
    rwa [conjugate_subgroup_map] at mapped

end CFSG.SignalizerFunctor.Helpers
