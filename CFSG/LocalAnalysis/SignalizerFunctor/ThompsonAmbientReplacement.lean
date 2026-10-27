module

public import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonSubgroupTransport
public import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonNormalizedReplacement

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem subgroupOf_derived_map (normal parent : Subgroup GroupType) (contained : normal ≤ parent) :
    (⁅normal.subgroupOf parent, normal.subgroupOf parent⁆).map parent.subtype = ⁅normal, normal⁆ := by
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le contained]

theorem maximum_order_abelian_ambient_normalized_replacement
    (prime : ℕ) (prime_prime : prime.Prime) (odd_prime : prime ≠ 2)
    (parent normal : Subgroup GroupType) [normal.Normal]
    (pgroup : IsPGroup prime parent) (contained : normal ≤ parent)
    (class_two : ⁅normal, normal⁆ ≤ Subgroup.centralizer (normal : Set GroupType))
    (derived_le : ⁅normal, normal⁆ ≤ embeddedOrderThompsonCenter parent)
    (omits : ¬ normal ≤ embeddedOrderThompsonCenter parent) :
    ∃ target : Subgroup parent,
      target ∈ maximumOrderAbelianFamily parent ∧
      ¬ normal ≤ target.map parent.subtype ∧
      normal ≤ Subgroup.normalizer (target.map parent.subtype : Set GroupType) := by
  let internal := normal.subgroupOf parent
  have internal_derived_le : ⁅internal, internal⁆ ≤ orderThompsonCenter parent := by
    intro element member
    have mapped_member := Subgroup.mem_map_of_mem parent.subtype member
    rw [subgroupOf_derived_map normal parent contained] at mapped_member
    obtain ⟨original, original_member, equal⟩ := derived_le mapped_member
    have equality : original = element := Subtype.ext equal
    exact equality ▸ original_member
  have internal_class_two : ⁅internal, internal⁆ ≤ Subgroup.centralizer (internal : Set parent) := by
    intro element member
    have mapped_member := Subgroup.mem_map_of_mem parent.subtype member
    rw [subgroupOf_derived_map normal parent contained] at mapped_member
    have central := class_two mapped_member
    apply Subgroup.mem_centralizer_iff.mpr
    intro other other_member
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp central other.val other_member
  have internal_omits : ¬ internal ≤ orderThompsonCenter parent := by
    intro internal_le
    apply omits
    have mapped_le := Subgroup.map_mono (f := parent.subtype) internal_le
    rwa [Subgroup.map_subgroupOf_eq_of_le contained] at mapped_le
  have witness_exists : ∃ witness ∈ maximumOrderAbelianFamily parent, ¬ internal ≤ witness := by
    by_contra! no_witness
    apply internal_omits
    rw [order_thompson_center_eq_intersection]
    exact le_iInf fun target => le_iInf fun member => no_witness target member
  obtain ⟨witness, witness_member, witness_omits⟩ := witness_exists
  obtain ⟨target, target_member, target_omits, normalized⟩ :=
    maximum_order_abelian_normalized_replacement prime prime_prime odd_prime pgroup internal
      internal_class_two internal_derived_le witness witness_member witness_omits
  refine ⟨target, target_member, ?_, ?_⟩
  · intro ambient_le
    apply target_omits
    intro element member
    obtain ⟨original, original_member, equal⟩ := ambient_le member
    have equality : original = element := Subtype.ext equal
    exact equality ▸ original_member
  · apply Subgroup.le_normalizer_iff.mpr
    intro conjugator conjugator_member element member
    obtain ⟨original, original_member, rfl⟩ := member
    refine ⟨(⟨conjugator, contained conjugator_member⟩ : parent) * original *
      (⟨conjugator, contained conjugator_member⟩ : parent)⁻¹, ?_, rfl⟩
    exact Subgroup.le_normalizer_iff.mp normalized ⟨conjugator, contained conjugator_member⟩
      conjugator_member original original_member

end CFSG.SignalizerFunctor.Helpers
