module

public import CFSG.LocalAnalysis.SignalizerFunctor.ProductPrimeParts
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerNormalCore
public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleParentProducts

public section

open CFSG.Open

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem invariant_normal_core
    {ActorType : Type actorUniverse} [Group ActorType]
    {GroupType : Type groupUniverse} [Group GroupType] [MulDistribMulAction ActorType GroupType]
    (subgroup : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup, actorElement • element ∈ subgroup) :
    ∀ actorElement : ActorType, ∀ element ∈ subgroup.normalCore,
      actorElement • element ∈ subgroup.normalCore := by
  intro actorElement element member
  let equivalence := MulDistribMulAction.toMulEquiv GroupType actorElement
  have subgroup_eq : subgroup.map equivalence.toMonoidHom = subgroup := by
    ext representative
    constructor
    · rintro ⟨preimage, preimage_member, rfl⟩
      exact invariant actorElement preimage preimage_member
    · intro representative_member
      exact ⟨actorElement⁻¹ • representative, invariant actorElement⁻¹ representative representative_member,
        smul_inv_smul actorElement representative⟩
  have core_eq := normal_core_map_automorphism subgroup equivalence
  rw [subgroup_eq] at core_eq
  have mapped_member := Subgroup.mem_map_of_mem equivalence.toMonoidHom member
  rw [core_eq] at mapped_member
  exact mapped_member

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem parent_normal_core_normalized (actor parent target : Subgroup GroupType)
    (parent_normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (target_normalized : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    actor ≤ Subgroup.normalizer
      (((target.subgroupOf parent).normalCore.map parent.subtype : Subgroup GroupType) : Set GroupType) := by
  let _action := conjugationAction actor parent parent_normalized
  have invariant := normalized_subgroupOf_invariant actor parent target parent_normalized target_normalized
  exact invariant_subgroup_map_normalized actor parent parent_normalized _
    (invariant_normal_core _ invariant)

theorem incomplete_full_parent_centralizers_compatible_core_trivial
    (prime rank : ℕ) (prime_prime : prime.Prime) (actor parent target : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType) (coprime : Nat.Coprime prime (Nat.card parent))
    (parent_normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (full : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected ⊓ parent = parent ⊓ Subgroup.centralizer (selected : Set GroupType))
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (incomplete : ¬ solvableSignalizerCompatible prime rank actor values parent)
    (compatible : solvableSignalizerCompatible prime rank actor values target) (target_le : target ≤ parent) :
    (target.subgroupOf parent).normalCore = ⊥ := by
  let core := (target.subgroupOf parent).normalCore
  let embedded := core.map parent.subtype
  have embedded_le : embedded ≤ target :=
    (Subgroup.map_mono (f := parent.subtype) (target.subgroupOf parent).normalCore_le).trans
    (by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr target_le])
  have embedded_normalized := parent_normal_core_normalized actor parent target parent_normalized compatible.1.1
  have embedded_compatible := solvable_signalizer_compatible_of_le prime rank actor values target embedded
    compatible embedded_le embedded_normalized
  have embedded_internal : embedded.subgroupOf parent = core :=
    Subgroup.comap_map_eq_self_of_injective parent.subtype_injective core
  have embedded_normal : (embedded.subgroupOf parent).Normal := by
    rw [embedded_internal]
    infer_instance
  have trivial := incomplete_full_parent_centralizers_normal_compatible_trivial prime rank prime_prime actor
    parent embedded elementary large values coprime parent_normalized full locally_complete incomplete
    embedded_compatible (Subgroup.map_subtype_le core) embedded_normal
  exact (Subgroup.map_eq_bot_iff_of_injective _ parent.subtype_injective).mp trivial

omit [Finite GroupType] in
theorem parent_subgroup_product_whole (parent first second : Subgroup GroupType)
    (first_le : first ≤ parent) (second_le : second ≤ parent)
    (whole : subgroupProduct first second = (parent : Set GroupType)) :
    subgroupProduct (first.subgroupOf parent) (second.subgroupOf parent) = Set.univ := by
  apply (subgroup_product_eq_univ_iff _ _).mpr
  intro element
  obtain ⟨firstElement, first_member, secondElement, second_member, product⟩ :=
    (subgroup_product_eq_subgroup_iff parent first second first_le second_le).mp whole element.val element.property
  exact ⟨⟨firstElement, first_le first_member⟩, first_member,
    ⟨secondElement, second_le second_member⟩, second_member, Subtype.ext product⟩

theorem incomplete_signalizer_hall_product_corefree
    (prime rank : ℕ) (prime_prime : prime.Prime) (actor parent complement factor : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (parent_normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (incomplete : ¬ solvableSignalizerCompatible prime rank actor values parent)
    (complement_compatible : solvableSignalizerCompatible prime rank actor values complement)
    (factor_compatible : signalizerCompatible prime rank actor values factor)
    (complement_le : complement ≤ parent)
    (whole : subgroupProduct complement factor = (parent : Set GroupType)) :
    (complement.subgroupOf parent).normalCore = ⊥ := by
  have rank_large : prime ^ rank ≤ Nat.card actor := by
    apply le_trans _ large
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ prime_prime.pos
  have coprime := compatible_parent_product_coprime prime rank prime_prime actor parent elementary rank_large
    values conditions.coprime complement factor complement_compatible.1 factor_compatible whole
  have full := compatible_parent_product_full_centralizers prime rank prime_prime actor parent elementary rank_large
    values conditions.central conditions.coprime complement factor complement_compatible.1 factor_compatible whole
  exact incomplete_full_parent_centralizers_compatible_core_trivial prime rank prime_prime actor parent complement
    elementary large values coprime parent_normalized full locally_complete incomplete complement_compatible complement_le

end CFSG.SignalizerFunctor.Helpers
