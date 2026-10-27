module

public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductFitting
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerParentCore

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem fitting_subgroup_subgroupOf_map (parent target : Subgroup GroupType) (target_le : target ≤ parent) :
    ((fittingSubgroup (GroupType := target.subgroupOf parent)).map (target.subgroupOf parent).subtype).map
      parent.subtype = (fittingSubgroup (GroupType := target)).map target.subtype := by
  let equivalence := Subgroup.subgroupOfEquivOfLe target_le
  have equal := fitting_subgroup_map_isomorphism equivalence
  have mapped_eq := congrArg (Subgroup.map target.subtype) equal
  rw [Subgroup.map_map] at mapped_eq
  rw [Subgroup.map_map]
  have hom_eq : target.subtype.comp equivalence.toMonoidHom =
      parent.subtype.comp (target.subgroupOf parent).subtype := by
    ext element
    rfl
  rwa [hom_eq] at mapped_eq

theorem parent_corefree_hall_product_normalized_complement_trivial
    (prime : ℕ) (prime_prime : prime.Prime) (parent complement factor target : Subgroup GroupType)
    (complement_le : complement ≤ parent) (factor_le : factor ≤ parent) (target_le : target ≤ parent)
    (complement_coprime : Nat.Coprime prime (Nat.card complement))
    (factor_pgroup : IsPGroup prime factor) (whole : subgroupProduct complement factor = (parent : Set GroupType))
    (corefree : (complement.subgroupOf parent).normalCore = ⊥)
    (target_coprime : Nat.Coprime prime (Nat.card target))
    (normalized : factor ≤ Subgroup.normalizer (target : Set GroupType)) : target = ⊥ := by
  have internal_normalized : factor.subgroupOf parent ≤
      Subgroup.normalizer (target.subgroupOf parent : Set parent) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro factorElement factor_member element member
    exact Subgroup.le_normalizer_iff.mp normalized factorElement.val factor_member element.val member
  have internal_coprime : Nat.Coprime prime (Nat.card (complement.subgroupOf parent)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe complement_le).toEquiv]
  have internal_target_coprime : Nat.Coprime prime (Nat.card (target.subgroupOf parent)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe target_le).toEquiv]
  have internal_pgroup := factor_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe factor_le).symm
  have trivial := corefree_hall_product_normalized_complement_trivial prime prime_prime
    (complement.subgroupOf parent) (factor.subgroupOf parent) (target.subgroupOf parent) internal_coprime
    internal_pgroup (parent_subgroup_product_whole parent complement factor complement_le factor_le whole)
    corefree internal_target_coprime internal_normalized
  have mapped_eq := congrArg (Subgroup.map parent.subtype) trivial
  rwa [Subgroup.map_subgroupOf_eq_of_le target_le, Subgroup.map_bot] at mapped_eq

theorem parent_corefree_hall_product_fitting_le_factor
    (prime : ℕ) (prime_prime : prime.Prime) (parent complement factor target : Subgroup GroupType)
    (complement_le : complement ≤ parent) (factor_le : factor ≤ parent) (target_le : target ≤ parent)
    (complement_coprime : Nat.Coprime prime (Nat.card complement))
    (factor_pgroup : IsPGroup prime factor) (whole : subgroupProduct complement factor = (parent : Set GroupType))
    (corefree : (complement.subgroupOf parent).normalCore = ⊥) (factor_target : factor ≤ target) :
    (fittingSubgroup (GroupType := target)).map target.subtype ≤ factor := by
  have internal_coprime : Nat.Coprime prime (Nat.card (complement.subgroupOf parent)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe complement_le).toEquiv]
  have internal_pgroup := factor_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe factor_le).symm
  have internal_le : factor.subgroupOf parent ≤ target.subgroupOf parent :=
    Subgroup.comap_mono factor_target
  have contained := corefree_hall_product_fitting_le_factor prime prime_prime (complement.subgroupOf parent)
    (factor.subgroupOf parent) (target.subgroupOf parent) internal_coprime internal_pgroup
    (parent_subgroup_product_whole parent complement factor complement_le factor_le whole) corefree internal_le
  have mapped_le := Subgroup.map_mono (f := parent.subtype) contained
  rwa [fitting_subgroup_subgroupOf_map parent target target_le, Subgroup.map_subgroupOf_eq_of_le factor_le] at mapped_le

theorem parent_corefree_abelian_hall_product_fitting_eq_factor
    (prime : ℕ) (prime_prime : prime.Prime) (parent complement factor target : Subgroup GroupType)
    (complement_le : complement ≤ parent) (factor_le : factor ≤ parent) (target_le : target ≤ parent)
    (complement_coprime : Nat.Coprime prime (Nat.card complement))
    (factor_pgroup : IsPGroup prime factor) (whole : subgroupProduct complement factor = (parent : Set GroupType))
    (corefree : (complement.subgroupOf parent).normalCore = ⊥) (factor_target : factor ≤ target)
    (abelian : IsMulCommutative factor) (solvable : Group.IsSolvable target) :
    (fittingSubgroup (GroupType := target)).map target.subtype = factor ∧
      (factor.subgroupOf target).Normal := by
  let := solvable
  let := abelian
  have fitting_le := parent_corefree_hall_product_fitting_le_factor prime prime_prime parent complement factor target
    complement_le factor_le target_le complement_coprime factor_pgroup whole corefree factor_target
  have factor_le_fitting : factor ≤ (fittingSubgroup (GroupType := target)).map target.subtype := by
    intro element member
    have centralizes : (⟨element, factor_target member⟩ : target) ∈
        Subgroup.centralizer (fittingSubgroup (GroupType := target) : Set target) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro other other_member
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.le_centralizer factor member) other.val
        (fitting_le (Subgroup.mem_map_of_mem target.subtype other_member))
    exact Subgroup.mem_map_of_mem target.subtype (solvable_fitting_centralizer_le centralizes)
  have equal := le_antisymm fitting_le factor_le_fitting
  refine ⟨equal, ?_⟩
  have internal_eq : factor.subgroupOf target = fittingSubgroup := by
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_subgroupOf_eq_of_le factor_target]
    exact equal.symm
  rw [internal_eq]
  exact fitting_subgroup_normal

end CFSG.SignalizerFunctor.Helpers
