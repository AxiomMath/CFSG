module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedGrowth
public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleConjugation

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

def subgroupFamilyJoin (family : Set (Subgroup GroupType)) : Subgroup GroupType :=
  ⨆ subgroup ∈ family, subgroup

theorem subgroup_family_join_le (family : Set (Subgroup GroupType)) (bound : Subgroup GroupType)
    (contained : ∀ subgroup ∈ family, subgroup ≤ bound) : subgroupFamilyJoin family ≤ bound :=
  iSup_le fun subgroup => iSup_le fun member => contained subgroup member

theorem subgroup_family_le_join (family : Set (Subgroup GroupType)) (subgroup : Subgroup GroupType)
    (member : subgroup ∈ family) : subgroup ≤ subgroupFamilyJoin family :=
  le_iSup_of_le subgroup (le_iSup_of_le member le_rfl)

theorem invariant_subgroup_family_join_normalized (actor : Subgroup GroupType)
    (family : Set (Subgroup GroupType))
    (invariant : ∀ element ∈ actor, ∀ subgroup ∈ family, conjugateSubgroup element subgroup ∈ family) :
    actor ≤ Subgroup.normalizer (subgroupFamilyJoin family : Set GroupType) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator conjugator_member element member
  have mapped_le : (subgroupFamilyJoin family).map (MulAut.conj conjugator).toMonoidHom ≤
      subgroupFamilyJoin family := by
    unfold subgroupFamilyJoin
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro subgroup
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro subgroup_member
    exact subgroup_family_le_join family (conjugateSubgroup conjugator subgroup)
      (invariant conjugator conjugator_member subgroup subgroup_member)
  exact mapped_le (Subgroup.mem_map_of_mem _ member)

theorem normalized_conjugate_subgroup_le (actor target : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (element : GroupType) (member : element ∈ actor) : conjugateSubgroup element target ≤ target := by
  rintro _ ⟨original, original_member, rfl⟩
  exact Subgroup.le_normalizer_iff.mp normalized element member original original_member

theorem pgroup_invariant_family_normalizer_extension [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (parent : Subgroup GroupType)
    (pgroup : IsPGroup prime parent) (family subfamily : Set (Subgroup GroupType))
    (contained : ∀ subgroup ∈ family, subgroup ≤ parent)
    (invariant : ∀ element ∈ parent, ∀ subgroup ∈ family, conjugateSubgroup element subgroup ∈ family)
    (proper : subfamily ⊂ family) :
    ∃ subgroup : Subgroup GroupType, subgroup ∈ family ∧ subgroup ∉ subfamily ∧
      subgroup ≤ parent ⊓ Subgroup.normalizer (subgroupFamilyJoin subfamily : Set GroupType) := by
  classical
  suffices general_result : ∀ order : ℕ, ∀ parent : Subgroup GroupType,
      Nat.card parent = order → IsPGroup prime parent →
      ∀ family subfamily : Set (Subgroup GroupType),
        (∀ subgroup ∈ family, subgroup ≤ parent) →
        (∀ element ∈ parent, ∀ subgroup ∈ family, conjugateSubgroup element subgroup ∈ family) →
        subfamily ⊂ family →
        ∃ subgroup : Subgroup GroupType, subgroup ∈ family ∧ subgroup ∉ subfamily ∧
          subgroup ≤ parent ⊓ Subgroup.normalizer (subgroupFamilyJoin subfamily : Set GroupType) by
    exact general_result (Nat.card parent) parent rfl pgroup family subfamily contained invariant proper
  intro order
  induction order using Nat.strong_induction_on with
  | h order induction_hypothesis =>
    intro parent parent_card parent_pgroup family subfamily contained invariant proper
    let generated := subgroupFamilyJoin subfamily
    have generated_le : generated ≤ parent := subgroup_family_join_le subfamily parent
      (fun subgroup member => contained subgroup (proper.subset member))
    by_cases full : generated = parent
    · obtain ⟨subgroup, family_member, not_member⟩ := Set.exists_of_ssubset proper
      refine ⟨subgroup, family_member, not_member, le_inf (contained subgroup family_member) ?_⟩
      exact (contained subgroup family_member).trans (full.symm.le.trans Subgroup.le_normalizer)
    · have generated_proper : generated < parent := lt_of_le_of_ne generated_le full
      let property : Subgroup GroupType → Prop := fun intermediate => intermediate ≤ parent ∧ intermediate ≠ parent
      have generated_property : property generated := ⟨generated_le, full⟩
      obtain ⟨middle, generated_middle, maximal⟩ := Finite.exists_le_maximal generated_property
      have middle_proper : middle < parent := lt_of_le_of_ne maximal.prop.1 maximal.prop.2
      have normalizes_middle : parent ≤ Subgroup.normalizer (middle : Set GroupType) := by
        have growth := pgroup_normalizer_strict_growth prime prime_prime parent middle parent_pgroup middle_proper
        have normalizer_full : parent ⊓ Subgroup.normalizer (middle : Set GroupType) = parent := by
          by_contra not_full
          have equality := maximal.eq_of_le ⟨inf_le_left, not_full⟩ growth.le
          exact growth.ne equality
        exact normalizer_full.symm.le.trans inf_le_right
      let middleFamily : Set (Subgroup GroupType) := {subgroup | subgroup ∈ family ∧ subgroup ≤ middle}
      have subfamily_middle : subfamily ⊆ middleFamily := by
        intro subgroup member
        exact ⟨proper.subset member, (subgroup_family_le_join subfamily subgroup member).trans generated_middle⟩
      by_cases subfamily_equal : subfamily = middleFamily
      · have subfamily_invariant : ∀ element ∈ parent, ∀ subgroup ∈ subfamily,
            conjugateSubgroup element subgroup ∈ subfamily := by
          intro element element_member subgroup subgroup_member
          have middle_member := subfamily_middle subgroup_member
          rw [subfamily_equal]
          refine ⟨invariant element element_member subgroup middle_member.1, ?_⟩
          exact (Subgroup.map_mono (f := (MulAut.conj element).toMonoidHom) middle_member.2).trans
            (normalized_conjugate_subgroup_le parent middle normalizes_middle element element_member)
        have generated_normalized := invariant_subgroup_family_join_normalized parent subfamily subfamily_invariant
        obtain ⟨subgroup, family_member, not_member⟩ := Set.exists_of_ssubset proper
        exact ⟨subgroup, family_member, not_member,
          le_inf (contained subgroup family_member) ((contained subgroup family_member).trans generated_normalized)⟩
      · have middle_smaller : Nat.card middle < order := by
          rw [← parent_card]
          have card_le : Nat.card middle ≤ Nat.card parent :=
            Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le middle_proper.le)
          apply lt_of_le_of_ne card_le
          intro same_card
          exact middle_proper.ne (Subgroup.eq_of_le_of_card_ge middle_proper.le same_card.ge)
        have middle_pgroup : IsPGroup prime middle := parent_pgroup.to_le maximal.prop.1
        have middle_invariant : ∀ element ∈ middle, ∀ subgroup ∈ middleFamily,
            conjugateSubgroup element subgroup ∈ middleFamily := by
          intro element element_member subgroup subgroup_member
          refine ⟨invariant element (maximal.prop.1 element_member) subgroup subgroup_member.1, ?_⟩
          exact (Subgroup.map_mono (f := (MulAut.conj element).toMonoidHom) subgroup_member.2).trans
            (normalized_conjugate_subgroup_le middle middle Subgroup.le_normalizer element element_member)
        obtain ⟨subgroup, middle_member, not_member, normalizes⟩ :=
          induction_hypothesis (Nat.card middle) middle_smaller middle rfl middle_pgroup middleFamily subfamily
            (fun _ member => member.2) middle_invariant
            (Set.ssubset_iff_subset_ne.mpr ⟨subfamily_middle, subfamily_equal⟩)
        exact ⟨subgroup, middle_member.1, not_member,
          normalizes.trans (inf_le_inf_right _ maximal.prop.1)⟩

end CFSG.SignalizerFunctor.Helpers
