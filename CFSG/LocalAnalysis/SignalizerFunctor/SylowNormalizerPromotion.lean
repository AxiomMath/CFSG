module

public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageAmbientNormalizers

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem sylow_of_normalizer_containment (prime : ℕ) (prime_prime : prime.Prime)
    (parent : Subgroup GroupType) (internalSylow : Sylow prime parent)
    (normalizer_le : Subgroup.normalizer
      (((internalSylow : Subgroup parent).map parent.subtype : Subgroup GroupType) : Set GroupType) ≤ parent) :
    ∃ ambientSylow : Sylow prime GroupType,
      (ambientSylow : Subgroup GroupType) = (internalSylow : Subgroup parent).map parent.subtype := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let target := (internalSylow : Subgroup parent).map parent.subtype
  have target_pgroup : IsPGroup prime target := internalSylow.isPGroup'.map parent.subtype
  obtain ⟨ambientSylow, target_le⟩ := target_pgroup.exists_le_sylow
  have equal : target = (ambientSylow : Subgroup GroupType) := by
    let internal := target.subgroupOf (ambientSylow : Subgroup GroupType)
    let _nilpotent : Group.IsNilpotent (ambientSylow : Subgroup GroupType) := ambientSylow.isPGroup'.isNilpotent
    have internal_normalizer_le : Subgroup.normalizer (internal : Set (ambientSylow : Subgroup GroupType)) ≤ internal := by
      have mapped_le : (Subgroup.normalizer (internal : Set (ambientSylow : Subgroup GroupType))).map
          (ambientSylow : Subgroup GroupType).subtype ≤ target := by
        have normalizer_formula := normalizer_subtype_map (ambientSylow : Subgroup GroupType) internal
        rw [Subgroup.map_subgroupOf_eq_of_le target_le] at normalizer_formula
        have mapped_parent : (Subgroup.normalizer (internal : Set (ambientSylow : Subgroup GroupType))).map
            (ambientSylow : Subgroup GroupType).subtype ≤ parent := by
          rw [normalizer_formula]
          exact inf_le_right.trans normalizer_le
        have mapped_pgroup : IsPGroup prime
            ((Subgroup.normalizer (internal : Set (ambientSylow : Subgroup GroupType))).map
              (ambientSylow : Subgroup GroupType).subtype) :=
          (ambientSylow.isPGroup'.to_subgroup _).map (ambientSylow : Subgroup GroupType).subtype
        let mapped := (Subgroup.normalizer (internal : Set (ambientSylow : Subgroup GroupType))).map
          (ambientSylow : Subgroup GroupType).subtype
        have mapped_internal_pgroup : IsPGroup prime (mapped.subgroupOf parent) :=
          mapped_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe mapped_parent).symm
        have target_normalizer : target ≤ mapped := by
          change target ≤ (Subgroup.normalizer (internal : Set (ambientSylow : Subgroup GroupType))).map
            (ambientSylow : Subgroup GroupType).subtype
          rw [normalizer_formula]
          exact le_inf target_le Subgroup.le_normalizer
        have sylow_le : (internalSylow : Subgroup parent) ≤ mapped.subgroupOf parent := by
          intro element member
          exact target_normalizer (Subgroup.mem_map_of_mem parent.subtype member)
        have internal_eq := internalSylow.is_maximal' mapped_internal_pgroup sylow_le
        have mapped_eq := congrArg (Subgroup.map parent.subtype) internal_eq
        rw [Subgroup.map_subgroupOf_eq_of_le mapped_parent] at mapped_eq
        exact mapped_eq.le
      apply Subgroup.map_subtype_le_map_subtype.mp
      rw [Subgroup.map_subgroupOf_eq_of_le target_le]
      exact mapped_le
    have internal_eq : internal = ⊤ :=
      (normalizerCondition_iff_only_full_group_self_normalizing.mp
        (Group.normalizerCondition_of_isNilpotent (G := (ambientSylow : Subgroup GroupType)))) internal
        (le_antisymm internal_normalizer_le Subgroup.le_normalizer)
    have mapped_eq := congrArg (Subgroup.map (ambientSylow : Subgroup GroupType).subtype) internal_eq
    rw [Subgroup.map_subgroupOf_eq_of_le target_le, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at mapped_eq
    exact mapped_eq
  exact ⟨ambientSylow, equal.symm⟩

theorem pgroup_sylow_of_normalizer_pgroups (prime : ℕ) (prime_prime : prime.Prime)
    (target : Subgroup GroupType) (target_pgroup : IsPGroup prime target)
    (contains_pgroups : ∀ subgroup : Subgroup GroupType, IsPGroup prime subgroup →
      subgroup ≤ Subgroup.normalizer (target : Set GroupType) → subgroup ≤ target) :
    ∃ sylow : Sylow prime GroupType, (sylow : Subgroup GroupType) = target := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  obtain ⟨sylow, target_le⟩ := target_pgroup.exists_le_sylow
  let internal := target.subgroupOf (sylow : Subgroup GroupType)
  let _nilpotent : Group.IsNilpotent (sylow : Subgroup GroupType) := sylow.isPGroup'.isNilpotent
  have normalizer_le : Subgroup.normalizer (internal : Set (sylow : Subgroup GroupType)) ≤ internal := by
    let normalizer := Subgroup.normalizer (internal : Set (sylow : Subgroup GroupType))
    let embedded := normalizer.map (sylow : Subgroup GroupType).subtype
    have embedded_pgroup : IsPGroup prime embedded :=
      (sylow.isPGroup'.to_subgroup normalizer).map (sylow : Subgroup GroupType).subtype
    have normalized : embedded ≤ Subgroup.normalizer (target : Set GroupType) := by
      have formula := normalizer_subtype_map (sylow : Subgroup GroupType) internal
      rw [Subgroup.map_subgroupOf_eq_of_le target_le] at formula
      change normalizer.map (sylow : Subgroup GroupType).subtype ≤ _
      rw [formula]
      exact inf_le_right
    have contained := contains_pgroups embedded embedded_pgroup normalized
    intro element member
    exact contained (Subgroup.mem_map_of_mem (sylow : Subgroup GroupType).subtype member)
  have equal : internal = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G := (sylow : Subgroup GroupType)))) internal
      (le_antisymm normalizer_le Subgroup.le_normalizer)
  have mapped_eq := congrArg (Subgroup.map (sylow : Subgroup GroupType).subtype) equal
  rw [Subgroup.map_subgroupOf_eq_of_le target_le, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at mapped_eq
  exact ⟨sylow, mapped_eq.symm⟩

omit [Finite GroupType] in
theorem parent_sylow_normalizer_pgroup_le (prime : ℕ) (parent : Subgroup GroupType)
    (sylow : Sylow prime parent) (target : Subgroup GroupType) (target_le : target ≤ parent)
    (target_pgroup : IsPGroup prime target)
    (normalized : target ≤ Subgroup.normalizer
      (((sylow : Subgroup parent).map parent.subtype : Subgroup GroupType) : Set GroupType)) :
    target ≤ (sylow : Subgroup parent).map parent.subtype := by
  let internal := target.subgroupOf parent
  have internal_pgroup : IsPGroup prime internal :=
    target_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe target_le).symm
  have internal_normalized : internal ≤ Subgroup.normalizer (sylow : Set parent) := by
    have mapped_formula := normalizer_subtype_map parent (sylow : Subgroup parent)
    apply Subgroup.map_subtype_le_map_subtype.mp
    change internal.map parent.subtype ≤
      (Subgroup.normalizer ((sylow : Subgroup parent) : Set parent)).map parent.subtype
    rw [mapped_formula, Subgroup.map_subgroupOf_eq_of_le target_le]
    exact le_inf target_le normalized
  have formula := internal_pgroup.inf_normalizer_sylow sylow
  rw [inf_eq_left.mpr internal_normalized] at formula
  have internal_le : internal ≤ (sylow : Subgroup parent) := formula.le.trans inf_le_right
  have mapped_le := Subgroup.map_mono (f := parent.subtype) internal_le
  rwa [Subgroup.map_subgroupOf_eq_of_le target_le] at mapped_le

end CFSG.SignalizerFunctor.Helpers
