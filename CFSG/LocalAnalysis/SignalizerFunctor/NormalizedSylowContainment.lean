module

public import CFSG.LocalAnalysis.SignalizerFunctor.NormalizedSylowIntersections
public import CFSG.LocalAnalysis.SignalizerFunctor.SylowNormalizerPromotion

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem normalized_pgroup_actor_sylow_containing (prime sylowPrime : ℕ)
    (prime_prime : prime.Prime) (sylowPrime_prime : sylowPrime.Prime)
    (actor parent target : Subgroup GroupType) (actor_pgroup : IsPGroup prime actor)
    (parent_normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card parent)) (target_le : target ≤ parent)
    (target_pgroup : IsPGroup sylowPrime target)
    (target_normalized : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    ∃ sylow : Sylow sylowPrime parent, target ≤ (sylow : Subgroup parent).map parent.subtype ∧
      actor ≤ Subgroup.normalizer (((sylow : Subgroup parent).map parent.subtype : Subgroup GroupType) : Set GroupType) := by
  let _action := conjugationAction actor parent parent_normalized
  have internal_prime : IsPGroup sylowPrime (target.subgroupOf parent) :=
    target_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe target_le).symm
  obtain ⟨sylow, contains, invariant⟩ := invariant_sylow_containing prime sylowPrime prime_prime sylowPrime_prime
    actor_pgroup coprime (target.subgroupOf parent) internal_prime
    (normalized_subgroupOf_invariant actor parent target parent_normalized target_normalized)
  refine ⟨sylow, ?_, invariant_subgroup_map_normalized actor parent parent_normalized _
    ((invariant_sylow_subgroup_iff sylowPrime sylow).mp invariant)⟩
  have mapped := Subgroup.map_mono (f := parent.subtype) contains
  rwa [Subgroup.map_subgroupOf_eq_of_le target_le] at mapped

omit [Finite GroupType] in
theorem embedded_normal_sylow_intersection (prime : ℕ) (prime_prime : prime.Prime)
    (parent normal : Subgroup GroupType)
    (normalSylow : Sylow prime normal) (parentSylow : Sylow prime parent)
    (contained : (normalSylow : Subgroup normal).map normal.subtype ≤
      (parentSylow : Subgroup parent).map parent.subtype) :
    (parentSylow : Subgroup parent).map parent.subtype ⊓ normal =
      (normalSylow : Subgroup normal).map normal.subtype := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let embedded := (parentSylow : Subgroup parent).map parent.subtype
  let intersection := embedded ⊓ normal
  have intersection_pgroup : IsPGroup prime intersection := (parentSylow.isPGroup'.map parent.subtype).to_le inf_le_left
  have internal_pgroup : IsPGroup prime (intersection.subgroupOf normal) :=
    intersection_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe (show intersection ≤ normal from inf_le_right)).symm
  have internal_contains : (normalSylow : Subgroup normal) ≤ intersection.subgroupOf normal := by
    intro element member
    exact ⟨contained (Subgroup.mem_map_of_mem normal.subtype member), element.property⟩
  have internal_equal := normalSylow.is_maximal' internal_pgroup internal_contains
  have mapped := congrArg (Subgroup.map normal.subtype) internal_equal
  rwa [Subgroup.map_subgroupOf_eq_of_le (show intersection ≤ normal from inf_le_right)] at mapped

theorem parent_sylow_of_parent_normalizer_containment (prime : ℕ) (prime_prime : prime.Prime)
    (parent localParent : Subgroup GroupType) (local_le : localParent ≤ parent) (sylow : Sylow prime localParent)
    (normalizer_le : parent ⊓ Subgroup.normalizer
      (((sylow : Subgroup localParent).map localParent.subtype : Subgroup GroupType) : Set GroupType) ≤ localParent) :
    ∃ parentSylow : Sylow prime parent,
      (parentSylow : Subgroup parent).map parent.subtype = (sylow : Subgroup localParent).map localParent.subtype := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let target := (sylow : Subgroup localParent).map localParent.subtype
  have target_le : target ≤ parent := (Subgroup.map_subtype_le _).trans local_le
  have target_prime : IsPGroup prime (target.subgroupOf parent) :=
    (sylow.isPGroup'.map localParent.subtype).of_equiv (Subgroup.subgroupOfEquivOfLe target_le).symm
  obtain ⟨parentSylow, equal⟩ := pgroup_sylow_of_normalizer_pgroups prime prime_prime (target.subgroupOf parent)
    target_prime (by
      intro subgroup subgroup_prime subgroup_normalizes
      let embedded := subgroup.map parent.subtype
      have embedded_parent : embedded ≤ parent := Subgroup.map_subtype_le _
      have embedded_normalizes : embedded ≤ Subgroup.normalizer (target : Set GroupType) := by
        have mapped := Subgroup.map_mono (f := parent.subtype) subgroup_normalizes
        have formula := normalizer_subtype_map parent (target.subgroupOf parent)
        rw [Subgroup.map_subgroupOf_eq_of_le target_le] at formula
        rw [formula] at mapped
        exact mapped.trans inf_le_right
      have embedded_local : embedded ≤ localParent := (le_inf embedded_parent embedded_normalizes).trans normalizer_le
      have internal_prime : IsPGroup prime (embedded.subgroupOf localParent) :=
        (subgroup_prime.map parent.subtype).of_equiv (Subgroup.subgroupOfEquivOfLe embedded_local).symm
      have target_embedded : embedded ≤ target := by
        have internal_normalizes : embedded.subgroupOf localParent ≤
            Subgroup.normalizer (sylow : Set localParent) := by
          have formula := normalizer_subtype_map localParent (sylow : Subgroup localParent)
          intro element member
          have image_member : element.val ∈ (Subgroup.normalizer (sylow : Set localParent)).map localParent.subtype := by
            change element.val ∈ (Subgroup.normalizer ((sylow : Subgroup localParent) : Set localParent)).map localParent.subtype
            rw [formula]
            exact ⟨element.property, embedded_normalizes member⟩
          obtain ⟨representative, representative_member, image⟩ := image_member
          have elements : representative = element := Subtype.ext image
          rwa [← elements]
        have contains : embedded.subgroupOf localParent ≤ (sylow : Subgroup localParent) := by
          have formula := internal_prime.inf_normalizer_sylow sylow
          rw [inf_eq_left.mpr internal_normalizes] at formula
          exact (le_inf_iff.mp formula.le).2
        have mapped := Subgroup.map_mono (f := localParent.subtype) contains
        rwa [Subgroup.map_subgroupOf_eq_of_le embedded_local] at mapped
      intro element member
      exact target_embedded (Subgroup.mem_map_of_mem parent.subtype member))
  exact ⟨parentSylow, by rw [equal, Subgroup.map_subgroupOf_eq_of_le target_le]⟩

end CFSG.SignalizerFunctor.Helpers
