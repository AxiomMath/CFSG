module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedPointLifting
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantActions
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem mem_sup_of_normalizing
    {GroupType : Type groupUniverse} [Group GroupType]
    (normal other : Subgroup GroupType)
    (normalizes : other ≤ Subgroup.normalizer (normal : Set GroupType))
    (element : GroupType) :
    element ∈ normal ⊔ other ↔
      ∃ first ∈ normal, ∃ second ∈ other, first * second = element := by
  constructor
  · intro member
    let combined := normal ⊔ other
    have combined_normalizes : combined ≤ Subgroup.normalizer (normal : Set GroupType) :=
      sup_le Subgroup.le_normalizer normalizes
    let _normal : (normal.subgroupOf combined).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr combined_normalizes
    have internal_whole : normal.subgroupOf combined ⊔ other.subgroupOf combined = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
      exact Subgroup.subgroupOf_self _
    have internal_member : (⟨element, member⟩ : combined) ∈
        normal.subgroupOf combined ⊔ other.subgroupOf combined := by
      rw [internal_whole]
      trivial
    obtain ⟨first, first_member, second, second_member, product⟩ :=
      Subgroup.mem_sup_of_normal_left.mp internal_member
    exact ⟨first.val, first_member, second.val, second_member,
      congrArg (fun internal : combined => (internal : GroupType)) product⟩
  · rintro ⟨first, first_member, second, second_member, rfl⟩
    exact (normal ⊔ other).mul_mem (Subgroup.mem_sup_left first_member)
      (Subgroup.mem_sup_right second_member)

theorem fixed_points_normal_product
    (prime : ℕ) (prime_prime : prime.Prime)
    (ActorType : Type actorUniverse) [Group ActorType]
    (actor_pgroup : IsPGroup prime ActorType)
    (GroupType : Type groupUniverse) [Group GroupType]
    [MulDistribMulAction ActorType GroupType]
    (normal other : Subgroup GroupType) [normal.Normal]
    (normal_invariant : ∀ actorElement : ActorType, ∀ element ∈ normal,
      actorElement • element ∈ normal)
    (other_invariant : ∀ actorElement : ActorType, ∀ element ∈ other,
      actorElement • element ∈ other)
    (whole : normal ⊔ other = ⊤)
    (other_coprime : Nat.Coprime prime (Nat.card other)) :
    let _normalAction := invariantSubgroupAction normal normal_invariant
    let _otherAction := invariantSubgroupAction other other_invariant
    FixedPoints.subgroup ActorType GroupType =
      (FixedPoints.subgroup ActorType normal).map normal.subtype ⊔
        (FixedPoints.subgroup ActorType other).map other.subtype := by
  let _normalAction := invariantSubgroupAction normal normal_invariant
  let _otherAction := invariantSubgroupAction other other_invariant
  let _quotientAction := invariantQuotientAction normal normal_invariant
  let projection := QuotientGroup.mk' normal
  let restricted : other →* GroupType ⧸ normal := projection.comp other.subtype
  have surjective : Function.Surjective restricted := by
    intro target
    obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective normal target
    have member : element ∈ normal ⊔ other := by
      rw [whole]
      trivial
    obtain ⟨first, first_member, second, second_member, rfl⟩ :=
      Subgroup.mem_sup_of_normal_left.mp member
    refine ⟨⟨second, second_member⟩, ?_⟩
    change projection second = projection (first * second)
    have first_trivial : projection first = 1 :=
      (QuotientGroup.eq_one_iff first).mpr first_member
    rw [map_mul, first_trivial, one_mul]
  have kernel_coprime : Nat.Coprime prime (Nat.card restricted.ker) :=
    other_coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card restricted.ker)
  have equivariant : ∀ actorElement : ActorType, ∀ element : other,
      restricted (actorElement • element) = actorElement • restricted element := by
    intro actorElement element
    exact invariant_quotient_equivariant normal normal_invariant actorElement element.val
  apply le_antisymm
  · intro element fixed
    have quotient_fixed : ∀ actorElement : ActorType,
        actorElement • projection element = projection element := by
      intro actorElement
      rw [← invariant_quotient_equivariant normal normal_invariant, fixed]
    obtain ⟨representative, representative_maps, representative_fixed⟩ :=
      fixed_point_lifts prime prime_prime actor_pgroup restricted surjective equivariant
        kernel_coprime (projection element) quotient_fixed
    have representative_fixed_ambient : ∀ actorElement : ActorType,
        actorElement • representative.val = representative.val := by
      intro actorElement
      exact congrArg (fun internal : other => (internal : GroupType))
        (representative_fixed actorElement)
    have difference_normal : element * representative.val⁻¹ ∈ normal := by
      apply (QuotientGroup.eq_one_iff _).mp
      change projection (element * representative.val⁻¹) = 1
      rw [map_mul, map_inv]
      change projection element * (restricted representative)⁻¹ = 1
      rw [representative_maps, mul_inv_cancel]
    have difference_fixed : ∀ actorElement : ActorType,
        actorElement • (element * representative.val⁻¹) = element * representative.val⁻¹ := by
      intro actorElement
      rw [MulDistribMulAction.smul_mul, smul_inv', fixed, representative_fixed_ambient]
    have normal_fixed : (⟨element * representative.val⁻¹, difference_normal⟩ : normal) ∈
        FixedPoints.subgroup ActorType normal := by
      intro actorElement
      exact Subtype.ext (difference_fixed actorElement)
    have difference_member := Subgroup.mem_sup_left
      (T := (FixedPoints.subgroup ActorType other).map other.subtype)
      (Subgroup.mem_map_of_mem normal.subtype normal_fixed)
    have representative_member := Subgroup.mem_sup_right
      (S := (FixedPoints.subgroup ActorType normal).map normal.subtype)
      (Subgroup.mem_map_of_mem other.subtype
        (show representative ∈ FixedPoints.subgroup ActorType other from representative_fixed))
    have product_member := Subgroup.mul_mem _ difference_member representative_member
    simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, mul_assoc, inv_mul_cancel,
      mul_one] using product_member
  · apply sup_le
    · rintro element ⟨representative, fixed, rfl⟩ actorElement
      exact congrArg (fun internal : normal => (internal : GroupType)) (fixed actorElement)
    · rintro element ⟨representative, fixed, rfl⟩ actorElement
      exact congrArg (fun internal : other => (internal : GroupType)) (fixed actorElement)

theorem fixed_points_sup_of_normalizing
    (prime : ℕ) (prime_prime : prime.Prime)
    (ActorType : Type actorUniverse) [Group ActorType]
    (actor_pgroup : IsPGroup prime ActorType)
    (GroupType : Type groupUniverse) [Group GroupType]
    [MulDistribMulAction ActorType GroupType]
    (normal other : Subgroup GroupType)
    (normalizes : other ≤ Subgroup.normalizer (normal : Set GroupType))
    (normal_invariant : ∀ actorElement : ActorType, ∀ element ∈ normal,
      actorElement • element ∈ normal)
    (other_invariant : ∀ actorElement : ActorType, ∀ element ∈ other,
      actorElement • element ∈ other)
    (other_coprime : Nat.Coprime prime (Nat.card other)) :
    (normal ⊔ other) ⊓ FixedPoints.subgroup ActorType GroupType =
      (normal ⊓ FixedPoints.subgroup ActorType GroupType) ⊔
        (other ⊓ FixedPoints.subgroup ActorType GroupType) := by
  let combined := normal ⊔ other
  have combined_invariant : ∀ actorElement : ActorType, ∀ element ∈ combined,
      actorElement • element ∈ combined := by
    intro actorElement element member
    obtain ⟨first, first_member, second, second_member, rfl⟩ :=
      (mem_sup_of_normalizing normal other normalizes element).mp member
    rw [MulDistribMulAction.smul_mul]
    exact combined.mul_mem (Subgroup.mem_sup_left (normal_invariant actorElement first first_member))
      (Subgroup.mem_sup_right (other_invariant actorElement second second_member))
  let _combinedAction := invariantSubgroupAction combined combined_invariant
  let normalInternal := normal.subgroupOf combined
  let otherInternal := other.subgroupOf combined
  let _normal : normalInternal.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer normalizes)
  have normalInternal_invariant : ∀ actorElement : ActorType, ∀ element ∈ normalInternal,
      actorElement • element ∈ normalInternal := by
    intro actorElement element member
    exact normal_invariant actorElement element.val member
  have otherInternal_invariant : ∀ actorElement : ActorType, ∀ element ∈ otherInternal,
      actorElement • element ∈ otherInternal := by
    intro actorElement element member
    exact other_invariant actorElement element.val member
  have internal_whole : normalInternal ⊔ otherInternal = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self _
  have internal_coprime : Nat.Coprime prime (Nat.card otherInternal) := by
    have cardinality : Nat.card otherInternal = Nat.card other :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show other ≤ combined from le_sup_right)).toEquiv
    rw [cardinality]
    exact other_coprime
  have internal_fixed := fixed_points_normal_product prime prime_prime ActorType actor_pgroup
    combined normalInternal otherInternal normalInternal_invariant otherInternal_invariant
    internal_whole internal_coprime
  have internal_ambient : ∀ internal : Subgroup combined,
      ((internal ⊓ FixedPoints.subgroup ActorType combined).map combined.subtype) =
        internal.map combined.subtype ⊓ FixedPoints.subgroup ActorType GroupType := by
    intro internal
    rw [Subgroup.map_inf internal (FixedPoints.subgroup ActorType combined)
      combined.subtype combined.subtype_injective,
      invariant_subgroup_fixed_points_map combined combined_invariant]
    apply le_antisymm
    · exact inf_le_inf_left _ inf_le_right
    · exact le_inf inf_le_left
        (le_inf (inf_le_left.trans (Subgroup.map_subtype_le internal)) inf_le_right)
  rw [← invariant_subgroup_fixed_points_map combined combined_invariant, internal_fixed]
  rw [Subgroup.map_sup]
  rw [invariant_subgroup_fixed_points_map normalInternal normalInternal_invariant,
    invariant_subgroup_fixed_points_map otherInternal otherInternal_invariant,
    internal_ambient, internal_ambient,
    Subgroup.map_subgroupOf_eq_of_le le_sup_left,
    Subgroup.map_subgroupOf_eq_of_le le_sup_right]

end CFSG.SignalizerFunctor.Helpers
