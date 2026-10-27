module

public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantFusion
public import CFSG.LocalAnalysis.SignalizerFunctor.PGroupFamilyNormalizer

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

@[expose] def subgroupWeakClosure (target parent : Subgroup GroupType) : Subgroup GroupType :=
  ⨆ element : GroupType, ⨆ (_ : conjugateSubgroup element target ≤ parent), conjugateSubgroup element target

@[expose] def normalizedConjugateHull (actor target : Subgroup GroupType) : Subgroup GroupType :=
  ⨆ element : actor, conjugateSubgroup element.val target

theorem subgroup_weak_closure_le (target parent : Subgroup GroupType) : subgroupWeakClosure target parent ≤ parent :=
  iSup_le fun _ => iSup_le fun contained => contained

theorem conjugate_le_weak_closure (target parent : Subgroup GroupType) (element : GroupType)
    (contained : conjugateSubgroup element target ≤ parent) :
    conjugateSubgroup element target ≤ subgroupWeakClosure target parent :=
  le_iSup_of_le element (le_iSup_of_le contained le_rfl)

theorem subgroup_weak_closure_mono (target first second : Subgroup GroupType) (contained : first ≤ second) :
    subgroupWeakClosure target first ≤ subgroupWeakClosure target second := by
  exact iSup_le fun element => iSup_le fun member => conjugate_le_weak_closure target second element
    (member.trans contained)

theorem subgroup_le_weak_closure (target parent : Subgroup GroupType) (contained : target ≤ parent) :
    target ≤ subgroupWeakClosure target parent := by
  have identity : conjugateSubgroup 1 target ≤ parent := by rwa [conjugate_subgroup_one]
  have included : conjugateSubgroup (1 : GroupType) target ≤ subgroupWeakClosure target parent :=
    le_iSup_of_le (1 : GroupType) (le_iSup_of_le identity le_rfl)
  simpa only [conjugate_subgroup_one] using included

theorem subgroup_le_normalized_conjugate_hull (actor target : Subgroup GroupType) :
    target ≤ normalizedConjugateHull actor target := by
  have included : conjugateSubgroup (1 : actor).val target ≤ normalizedConjugateHull actor target :=
    le_iSup_of_le (1 : actor) le_rfl
  simpa only [Subgroup.coe_one, conjugate_subgroup_one] using included

theorem normalized_conjugate_hull_normalized (actor target : Subgroup GroupType) :
    actor ≤ Subgroup.normalizer (normalizedConjugateHull actor target : Set GroupType) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator conjugator_member element member
  have map_le : (normalizedConjugateHull actor target).map (MulAut.conj conjugator).toMonoidHom ≤
      normalizedConjugateHull actor target := by
    unfold normalizedConjugateHull
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro actorElement
    change conjugateSubgroup conjugator (conjugateSubgroup actorElement.val target) ≤ _
    rw [conjugate_subgroup_mul]
    exact le_iSup_of_le (⟨conjugator * actorElement.val, actor.mul_mem conjugator_member actorElement.property⟩ : actor)
      le_rfl
  exact map_le (Subgroup.mem_map_of_mem _ member)

theorem normalized_conjugate_hull_le (actor target bound : Subgroup GroupType)
    (contained : target ≤ bound) (normalized : actor ≤ Subgroup.normalizer (bound : Set GroupType)) :
    normalizedConjugateHull actor target ≤ bound := by
  apply iSup_le
  intro actorElement
  exact (Subgroup.map_mono (f := (MulAut.conj actorElement.val).toMonoidHom) contained).trans
    (normalized_conjugate_subgroup_le actor bound normalized actorElement.val actorElement.property)

theorem matsuyama_weak_closure [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (actor target : Subgroup GroupType)
    (orbit_pgroup : ∀ element : GroupType,
      IsPGroup prime (normalizedConjugateHull actor (conjugateSubgroup element target))) :
    ∃ sylow : Sylow prime GroupType, target ≤ (sylow : Subgroup GroupType) ∧
      actor ≤ Subgroup.normalizer (subgroupWeakClosure target sylow : Set GroupType) := by
  classical
  let property : Subgroup GroupType → Prop := fun subgroup => IsPGroup prime subgroup ∧
    actor ≤ Subgroup.normalizer (subgroup : Set GroupType) ∧ target ≤ subgroup ∧
    subgroupWeakClosure target subgroup = subgroup
  let initial := normalizedConjugateHull actor target
  have initial_pgroup : IsPGroup prime initial := by
    have identity : conjugateSubgroup (1 : GroupType) target = target := conjugate_subgroup_one target
    have initial_result := orbit_pgroup 1
    rw [identity] at initial_result
    exact initial_result
  have initial_property : property initial := by
    refine ⟨initial_pgroup, normalized_conjugate_hull_normalized actor target,
      subgroup_le_normalized_conjugate_hull actor target, le_antisymm (subgroup_weak_closure_le target initial) ?_⟩
    apply iSup_le
    intro actorElement
    have contained : conjugateSubgroup actorElement.val target ≤ initial := le_iSup_of_le actorElement le_rfl
    exact le_iSup_of_le actorElement.val (le_iSup_of_le contained le_rfl)
  obtain ⟨maximalGroup, _, maximal⟩ := Finite.exists_le_maximal initial_property
  obtain ⟨sylow, maximal_sylow⟩ := maximal.prop.1.exists_le_sylow
  let parent : Subgroup GroupType := sylow
  let family : Set (Subgroup GroupType) := {subgroup | (∃ element : GroupType,
    conjugateSubgroup element target = subgroup) ∧ subgroup ≤ parent}
  let subfamily : Set (Subgroup GroupType) := {subgroup | subgroup ∈ family ∧ subgroup ≤ maximalGroup}
  have family_contained : ∀ subgroup ∈ family, subgroup ≤ parent := fun _ member => member.2
  have family_invariant : ∀ element ∈ parent, ∀ subgroup ∈ family,
      conjugateSubgroup element subgroup ∈ family := by
    rintro element element_member subgroup ⟨⟨original, rfl⟩, contained⟩
    refine ⟨⟨element * original, (conjugate_subgroup_mul element original target).symm⟩, ?_⟩
    exact (Subgroup.map_mono (f := (MulAut.conj element).toMonoidHom) contained).trans
      (normalized_conjugate_subgroup_le parent parent Subgroup.le_normalizer element element_member)
  have subfamily_join : subgroupFamilyJoin subfamily = maximalGroup := by
    apply le_antisymm (subgroup_family_join_le subfamily maximalGroup (fun _ member => member.2))
    rw [← maximal.prop.2.2.2]
    apply iSup_le
    intro element
    apply iSup_le
    intro contained
    exact subgroup_family_le_join subfamily (conjugateSubgroup element target)
      ⟨⟨⟨element, rfl⟩, contained.trans maximal_sylow⟩, contained⟩
  have family_equal : subfamily = family := by
    by_contra not_equal
    have proper : subfamily ⊂ family := Set.ssubset_iff_subset_ne.mpr ⟨fun _ member => member.1, not_equal⟩
    obtain ⟨subgroup, family_member, outside, normalizes⟩ := pgroup_invariant_family_normalizer_extension
      prime prime_prime parent sylow.isPGroup' family subfamily family_contained family_invariant proper
    rw [subfamily_join] at normalizes
    obtain ⟨element, conjugate_equal⟩ := family_member.1
    let orbit := normalizedConjugateHull actor subgroup
    have orbit_pgroup' : IsPGroup prime orbit := by
      change IsPGroup prime (normalizedConjugateHull actor subgroup)
      rw [← conjugate_equal]
      exact orbit_pgroup element
    have orbit_normalizes : orbit ≤ Subgroup.normalizer (maximalGroup : Set GroupType) :=
      normalized_conjugate_hull_le actor subgroup _ (normalizes.trans inf_le_right)
        (normalizer_normalized actor maximalGroup maximal.prop.2.1)
    have enlarged_property : property (maximalGroup ⊔ orbit) := by
      refine ⟨maximal.prop.1.to_sup_of_normal_left' orbit_pgroup' orbit_normalizes, ?_,
        maximal.prop.2.2.1.trans le_sup_left, ?_⟩
      · apply (le_inf maximal.prop.2.1 (normalized_conjugate_hull_normalized actor subgroup)).trans
        exact Subgroup.inf_normalizer_le_normalizer_sup maximalGroup orbit
      · apply le_antisymm (subgroup_weak_closure_le target _)
        apply sup_le
        · exact maximal.prop.2.2.2.symm.le.trans
            (subgroup_weak_closure_mono target maximalGroup (maximalGroup ⊔ orbit) le_sup_left)
        · apply iSup_le
          intro actorElement
          have orbit_term_le : conjugateSubgroup actorElement.val subgroup ≤ maximalGroup ⊔ orbit :=
            (show conjugateSubgroup actorElement.val subgroup ≤ orbit from le_iSup_of_le actorElement le_rfl).trans
              le_sup_right
          have term_equal : conjugateSubgroup actorElement.val subgroup =
              conjugateSubgroup (actorElement.val * element) target := by
            rw [← conjugate_equal, conjugate_subgroup_mul]
          rw [term_equal] at orbit_term_le ⊢
          exact conjugate_le_weak_closure target (maximalGroup ⊔ orbit) (actorElement.val * element) orbit_term_le
    have maximal_equal := maximal.eq_of_le enlarged_property le_sup_left
    have subgroup_le : subgroup ≤ maximalGroup :=
      (subgroup_le_normalized_conjugate_hull actor subgroup).trans (le_sup_right.trans maximal_equal.symm.le)
    exact outside ⟨family_member, subgroup_le⟩
  have weak_closure_equal : subgroupWeakClosure target parent = maximalGroup := by
    apply le_antisymm
    · apply iSup_le
      intro element
      apply iSup_le
      intro contained
      have member : conjugateSubgroup element target ∈ family := ⟨⟨element, rfl⟩, contained⟩
      rw [← family_equal] at member
      exact member.2
    · exact maximal.prop.2.2.2.symm.le.trans (subgroup_weak_closure_mono target maximalGroup parent maximal_sylow)
  refine ⟨sylow, maximal.prop.2.2.1.trans maximal_sylow, ?_⟩
  rw [weak_closure_equal]
  exact maximal.prop.2.1

end CFSG.SignalizerFunctor.Helpers
