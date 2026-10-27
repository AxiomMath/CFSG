module

public import CFSG.LocalAnalysis.SignalizerFunctor.MatsuyamaWeakClosure

public section

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

@[expose] def relativeWeakClosure (parent target bound : Subgroup GroupType) : Subgroup GroupType :=
  ⨆ conjugator : parent, ⨆ (_ : conjugateSubgroup conjugator.val target ≤ bound),
    conjugateSubgroup conjugator.val target

theorem relative_weak_closure_le (parent target bound : Subgroup GroupType) :
    relativeWeakClosure parent target bound ≤ bound := iSup_le fun _ => iSup_le fun contained => contained

theorem relative_weak_closure_mono (parent target first second : Subgroup GroupType) (contained : first ≤ second) :
    relativeWeakClosure parent target first ≤ relativeWeakClosure parent target second := by
  apply iSup_le
  intro conjugator
  apply iSup_le
  intro member
  exact le_iSup_of_le conjugator (le_iSup_of_le (member.trans contained) le_rfl)

theorem subgroup_le_relative_weak_closure (parent target bound : Subgroup GroupType) (contained : target ≤ bound) :
    target ≤ relativeWeakClosure parent target bound := by
  have identity : conjugateSubgroup (1 : parent).val target = target := conjugate_subgroup_one target
  exact identity.ge.trans (le_iSup_of_le (1 : parent) (le_iSup_of_le (identity.le.trans contained) le_rfl))

theorem normalized_conjugate_hull_map {ImageType : Type imageUniverse} [Group ImageType]
    (homomorphism : GroupType →* ImageType) (actor target : Subgroup GroupType) :
    (normalizedConjugateHull actor target).map homomorphism =
      normalizedConjugateHull (actor.map homomorphism) (target.map homomorphism) := by
  unfold normalizedConjugateHull
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro actorElement
    rw [conjugate_subgroup_map]
    exact le_iSup_of_le (⟨homomorphism actorElement.val, Subgroup.mem_map_of_mem _ actorElement.property⟩ : actor.map homomorphism)
      le_rfl
  · apply iSup_le
    intro actorElement
    obtain ⟨original, original_member, equal⟩ := actorElement.property
    have term : (conjugateSubgroup original target).map homomorphism ≤
        ⨆ internal : actor, (conjugateSubgroup internal.val target).map homomorphism :=
      le_iSup_of_le (⟨original, original_member⟩ : actor) le_rfl
    rwa [conjugate_subgroup_map, equal] at term

theorem relative_weak_closure_map_subtype (parent target bound : Subgroup GroupType)
    (target_le : target ≤ parent) (bound_le : bound ≤ parent) :
    (subgroupWeakClosure (target.subgroupOf parent) (bound.subgroupOf parent)).map parent.subtype =
      relativeWeakClosure parent target bound := by
  unfold subgroupWeakClosure relativeWeakClosure
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro conjugator
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro contained
    have mapped_contained := Subgroup.map_mono (f := parent.subtype) contained
    rw [conjugate_subgroup_map, Subgroup.map_subgroupOf_eq_of_le target_le,
      Subgroup.map_subgroupOf_eq_of_le bound_le] at mapped_contained
    rw [conjugate_subgroup_map, Subgroup.map_subgroupOf_eq_of_le target_le]
    exact le_iSup_of_le conjugator (le_iSup_of_le mapped_contained le_rfl)
  · apply iSup_le
    intro conjugator
    apply iSup_le
    intro contained
    have internal_contained : conjugateSubgroup conjugator (target.subgroupOf parent) ≤ bound.subgroupOf parent := by
      intro element member
      have mapped_member := Subgroup.mem_map_of_mem parent.subtype member
      rw [conjugate_subgroup_map, Subgroup.map_subgroupOf_eq_of_le target_le] at mapped_member
      exact contained mapped_member
    have term : (conjugateSubgroup conjugator (target.subgroupOf parent)).map parent.subtype ≤
        ⨆ internal : parent, (⨆ (_ : conjugateSubgroup internal (target.subgroupOf parent) ≤ bound.subgroupOf parent),
          conjugateSubgroup internal (target.subgroupOf parent)).map parent.subtype := by
      apply le_iSup_of_le conjugator
      exact Subgroup.map_mono (le_iSup_of_le internal_contained le_rfl)
    rwa [conjugate_subgroup_map, Subgroup.map_subgroupOf_eq_of_le target_le] at term

theorem relative_weak_closure_normalized (external parent target bound : Subgroup GroupType)
    (parent_normalized : external ≤ Subgroup.normalizer (parent : Set GroupType))
    (target_normalized : external ≤ Subgroup.normalizer (target : Set GroupType))
    (bound_normalized : external ≤ Subgroup.normalizer (bound : Set GroupType)) :
    external ≤ Subgroup.normalizer (relativeWeakClosure parent target bound : Set GroupType) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator conjugator_member element member
  have image_le : (relativeWeakClosure parent target bound).map (MulAut.conj conjugator).toMonoidHom ≤
      relativeWeakClosure parent target bound := by
    unfold relativeWeakClosure
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro original
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro contained
    change conjugateSubgroup conjugator (conjugateSubgroup original.val target) ≤ _
    have equal : conjugateSubgroup conjugator (conjugateSubgroup original.val target) =
        conjugateSubgroup (conjugator * original.val * conjugator⁻¹) target := by
      have preserved := Subgroup.mem_normalizer_iff_map_conj_eq.mp (target_normalized conjugator_member)
      change conjugateSubgroup conjugator target = target at preserved
      calc
        _ = conjugateSubgroup (conjugator * original.val * conjugator⁻¹)
            (conjugateSubgroup conjugator target) := by
          rw [conjugate_subgroup_mul, conjugate_subgroup_mul]
          congr 1
          group
        _ = _ := by rw [preserved]
    have new_contained : conjugateSubgroup (conjugator * original.val * conjugator⁻¹) target ≤ bound := by
      rw [← equal]
      exact (Subgroup.map_mono (f := (MulAut.conj conjugator).toMonoidHom) contained).trans
        (normalized_conjugate_subgroup_le external bound bound_normalized conjugator conjugator_member)
    rw [equal]
    exact le_iSup_of_le (⟨conjugator * original.val * conjugator⁻¹,
      Subgroup.le_normalizer_iff.mp parent_normalized conjugator conjugator_member original.val original.property⟩ : parent)
      (le_iSup_of_le new_contained le_rfl)
  exact image_le (Subgroup.mem_map_of_mem _ member)

theorem relative_weak_closure_parent_normalizer (parent target bound : Subgroup GroupType) :
    parent ⊓ Subgroup.normalizer (bound : Set GroupType) ≤
      Subgroup.normalizer (relativeWeakClosure parent target bound : Set GroupType) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator conjugator_member element member
  have image_le : (relativeWeakClosure parent target bound).map (MulAut.conj conjugator).toMonoidHom ≤
      relativeWeakClosure parent target bound := by
    unfold relativeWeakClosure
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro original
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro contained
    change conjugateSubgroup conjugator (conjugateSubgroup original.val target) ≤ _
    rw [conjugate_subgroup_mul]
    have new_contained : conjugateSubgroup (conjugator * original.val) target ≤ bound := by
      rw [← conjugate_subgroup_mul]
      exact (Subgroup.map_mono (f := (MulAut.conj conjugator).toMonoidHom) contained).trans
        (normalized_conjugate_subgroup_le (Subgroup.normalizer (bound : Set GroupType)) bound le_rfl
          conjugator conjugator_member.2)
    exact le_iSup_of_le (⟨conjugator * original.val, parent.mul_mem conjugator_member.1 original.property⟩ : parent)
      (le_iSup_of_le new_contained le_rfl)
  exact image_le (Subgroup.mem_map_of_mem _ member)

theorem relative_weak_closure_idempotent (parent target bound : Subgroup GroupType) :
    relativeWeakClosure parent target (relativeWeakClosure parent target bound) =
      relativeWeakClosure parent target bound := by
  apply le_antisymm
    (relative_weak_closure_mono parent target _ bound (relative_weak_closure_le parent target bound))
  apply iSup_le
  intro conjugator
  apply iSup_le
  intro contained
  have term_le : conjugateSubgroup conjugator.val target ≤ relativeWeakClosure parent target bound :=
    le_iSup_of_le conjugator (le_iSup_of_le contained le_rfl)
  exact le_iSup_of_le conjugator (le_iSup_of_le term_le le_rfl)

theorem normalized_orbit_relative_weak_closure (parent actor target : Subgroup GroupType) (actor_le : actor ≤ parent) :
    relativeWeakClosure parent target (normalizedConjugateHull actor target) = normalizedConjugateHull actor target := by
  apply le_antisymm (relative_weak_closure_le parent target _)
  apply iSup_le
  intro actorElement
  have term_le : conjugateSubgroup actorElement.val target ≤ normalizedConjugateHull actor target :=
    le_iSup_of_le actorElement le_rfl
  exact le_iSup_of_le (⟨actorElement.val, actor_le actorElement.property⟩ : parent) (le_iSup_of_le term_le le_rfl)

end CFSG.SignalizerFunctor.Helpers
