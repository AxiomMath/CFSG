module

public import CFSG.LocalAnalysis.SignalizerFunctor.ParentHallFitting
public import CFSG.LocalAnalysis.SignalizerFunctor.SylowNormalizerPromotion

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

structure IncompleteSignalizerHallProduct (prime rank groupPrime : ℕ)
    (actor parent complement factor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) : Prop where
  prime_prime : prime.Prime
  groupPrime_prime : groupPrime.Prime
  elementary : IsElemAbelian prime actor
  large : prime ^ (rank + 1) ≤ Nat.card actor
  conditions : SolvableSignalizerConditions prime rank actor values
  parent_normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType)
  locally_complete : solvableSignalizerLocallyComplete prime rank actor values
  incomplete : ¬ solvableSignalizerCompatible prime rank actor values parent
  complement_compatible : solvableSignalizerCompatible prime rank actor values complement
  factor_compatible : signalizerCompatible prime rank actor values factor
  complement_le : complement ≤ parent
  factor_le : factor ≤ parent
  complement_coprime : Nat.Coprime groupPrime (Nat.card complement)
  factor_pgroup : IsPGroup groupPrime factor
  whole : subgroupProduct complement factor = (parent : Set GroupType)

variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_hall_product_corefree
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values) :
    (complement.subgroupOf parent).normalCore = ⊥ :=
  incomplete_signalizer_hall_product_corefree prime rank datum.prime_prime actor parent complement factor
    datum.elementary datum.large values datum.conditions datum.parent_normalized datum.locally_complete
    datum.incomplete datum.complement_compatible datum.factor_compatible datum.complement_le datum.whole

theorem incomplete_hall_product_parent_coprime
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values) :
    Nat.Coprime prime (Nat.card parent) := by
  have rank_large : prime ^ rank ≤ Nat.card actor := by
    apply le_trans _ datum.large
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ datum.prime_prime.pos
  exact compatible_parent_product_coprime prime rank datum.prime_prime actor parent datum.elementary rank_large
    values datum.conditions.coprime complement factor datum.complement_compatible.1 datum.factor_compatible datum.whole

theorem incomplete_hall_product_full_centralizers
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values) :
    ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected ⊓ parent = parent ⊓ Subgroup.centralizer (selected : Set GroupType) := by
  have rank_large : prime ^ rank ≤ Nat.card actor := by
    apply le_trans _ datum.large
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ datum.prime_prime.pos
  exact compatible_parent_product_full_centralizers prime rank datum.prime_prime actor parent datum.elementary
    rank_large values datum.conditions.central datum.conditions.coprime complement factor
    datum.complement_compatible.1 datum.factor_compatible datum.whole

theorem incomplete_hall_product_normalized_compatible (target : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (target_le : target ≤ parent) (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    signalizerCompatible prime rank actor values target := by
  refine ⟨normalized, ?_⟩
  intro selected member
  exact (inf_le_inf_right _ target_le).trans
    ((incomplete_hall_product_full_centralizers datum selected member).symm.le.trans inf_le_left)

theorem incomplete_hall_product_normalizer_compatible (target : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (compatible : solvableSignalizerCompatible prime rank actor values target) (nontrivial : target ≠ ⊥) :
    solvableSignalizerCompatible prime rank actor values
      (parent ⊓ Subgroup.normalizer (target : Set GroupType)) :=
  full_parent_centralizers_locally_complete_normalizer_solvable prime rank datum.prime_prime actor parent target
    datum.elementary datum.large values (incomplete_hall_product_parent_coprime datum) datum.parent_normalized
    (incomplete_hall_product_full_centralizers datum) datum.locally_complete compatible nontrivial

omit [Finite GroupType] in
theorem incomplete_hall_product_factor_nontrivial
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values) : factor ≠ ⊥ := by
  intro trivial
  have parent_le : parent ≤ complement := by
    intro element member
    obtain ⟨firstElement, first_member, secondElement, second_member, product⟩ :=
      (subgroup_product_eq_subgroup_iff parent complement factor datum.complement_le datum.factor_le).mp
        datum.whole element member
    rw [trivial] at second_member
    have second_eq : secondElement = 1 := second_member
    rw [second_eq, mul_one] at product
    rwa [← product]
  have equal := le_antisymm datum.complement_le parent_le
  apply datum.incomplete
  rw [← equal]
  exact datum.complement_compatible

theorem incomplete_hall_product_normalized_complement_trivial (target : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (target_le : target ≤ parent) (target_coprime : Nat.Coprime groupPrime (Nat.card target))
    (normalized : factor ≤ Subgroup.normalizer (target : Set GroupType)) : target = ⊥ :=
  parent_corefree_hall_product_normalized_complement_trivial groupPrime datum.groupPrime_prime parent complement factor
    target datum.complement_le datum.factor_le target_le datum.complement_coprime datum.factor_pgroup datum.whole
    (incomplete_hall_product_corefree datum) target_coprime normalized

theorem incomplete_hall_product_fitting_le_factor (target : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (target_le : target ≤ parent) (factor_target : factor ≤ target) :
    (fittingSubgroup (GroupType := target)).map target.subtype ≤ factor :=
  parent_corefree_hall_product_fitting_le_factor groupPrime datum.groupPrime_prime parent complement factor target
    datum.complement_le datum.factor_le target_le datum.complement_coprime datum.factor_pgroup datum.whole
    (incomplete_hall_product_corefree datum) factor_target

theorem incomplete_abelian_hall_product_fitting_eq_factor (target : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (target_le : target ≤ parent) (factor_target : factor ≤ target)
    (abelian : IsMulCommutative factor) (solvable : Group.IsSolvable target) :
    (fittingSubgroup (GroupType := target)).map target.subtype = factor ∧ (factor.subgroupOf target).Normal :=
  parent_corefree_abelian_hall_product_fitting_eq_factor groupPrime datum.groupPrime_prime parent complement factor target
    datum.complement_le datum.factor_le target_le datum.complement_coprime datum.factor_pgroup datum.whole
    (incomplete_hall_product_corefree datum) factor_target abelian solvable

theorem incomplete_abelian_hall_product_factor_normalizer_compatible
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) :
    solvableSignalizerCompatible prime rank actor values (parent ⊓ Subgroup.normalizer (factor : Set GroupType)) := by
  let := abelian
  exact incomplete_hall_product_normalizer_compatible factor datum
    ⟨datum.factor_compatible, Group.isSolvable_of_comm mul_comm'⟩ (incomplete_hall_product_factor_nontrivial datum)

theorem incomplete_abelian_hall_product_subgroup_normalizer_trap (target : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (target_le : target ≤ factor) (nontrivial : target ≠ ⊥)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    solvableSignalizerCompatible prime rank actor values (parent ⊓ Subgroup.normalizer (target : Set GroupType)) ∧
      parent ⊓ Subgroup.normalizer (target : Set GroupType) ≤ Subgroup.normalizer (factor : Set GroupType) := by
  let := abelian
  have target_compatible := solvable_signalizer_compatible_of_le prime rank actor values factor target
    ⟨datum.factor_compatible, Group.isSolvable_of_comm mul_comm'⟩ target_le normalized
  have normalizer_compatible := incomplete_hall_product_normalizer_compatible target datum target_compatible nontrivial
  have factor_normalizes : factor ≤ Subgroup.normalizer (target : Set GroupType) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    apply Subgroup.le_centralizer_iff.mpr
    exact target_le.trans (Subgroup.le_centralizer factor)
  have factor_normal := (incomplete_abelian_hall_product_fitting_eq_factor
    (parent ⊓ Subgroup.normalizer (target : Set GroupType)) datum inf_le_left
      (le_inf datum.factor_le factor_normalizes) abelian normalizer_compatible.2).2
  exact ⟨normalizer_compatible, (Subgroup.normal_subgroupOf_iff_le_normalizer
    (le_inf datum.factor_le factor_normalizes)).mp factor_normal⟩

theorem incomplete_hall_product_factor_parent_sylow
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values) :
    ∃ sylow : Sylow groupPrime parent, (sylow : Subgroup parent) = factor.subgroupOf parent := by
  have internal_coprime : Nat.Coprime groupPrime (Nat.card (complement.subgroupOf parent)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe datum.complement_le).toEquiv]
    exact datum.complement_coprime
  have internal_pgroup := datum.factor_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe datum.factor_le).symm
  exact (hall_product_orders groupPrime datum.groupPrime_prime (complement.subgroupOf parent)
    (factor.subgroupOf parent) internal_coprime internal_pgroup
    (parent_subgroup_product_whole parent complement factor datum.complement_le datum.factor_le datum.whole)).2.2.2

theorem incomplete_abelian_hall_product_sylow_intersection (target : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (target_le : target ≤ parent)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (nontrivial : target ⊓ factor ≠ ⊥) :
    ∃ sylow : Sylow groupPrime target, (sylow : Subgroup target) = factor.subgroupOf target := by
  let intersection := target ⊓ factor
  have intersection_le : intersection ≤ target := inf_le_left
  have intersection_pgroup : IsPGroup groupPrime intersection := datum.factor_pgroup.to_le inf_le_right
  have intersection_normalized : actor ≤ Subgroup.normalizer (intersection : Set GroupType) :=
    normalizer_inf_of_le actor _ _ normalized datum.factor_compatible.1
  have trap := incomplete_abelian_hall_product_subgroup_normalizer_trap intersection datum abelian
    inf_le_right nontrivial intersection_normalized
  obtain ⟨parentSylow, parentSylow_eq⟩ := incomplete_hall_product_factor_parent_sylow datum
  have parentSylow_embedded : (parentSylow : Subgroup parent).map parent.subtype = factor := by
    rw [parentSylow_eq, Subgroup.map_subgroupOf_eq_of_le datum.factor_le]
  have internal_pgroup : IsPGroup groupPrime (intersection.subgroupOf target) :=
    intersection_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe intersection_le).symm
  obtain ⟨sylow, sylow_eq⟩ := pgroup_sylow_of_normalizer_pgroups groupPrime datum.groupPrime_prime
    (intersection.subgroupOf target) internal_pgroup (by
      intro internal internal_prime internal_normalizes
      let embedded := internal.map target.subtype
      have embedded_le : embedded ≤ target := Subgroup.map_subtype_le _
      have embedded_parent : embedded ≤ parent := embedded_le.trans target_le
      have embedded_normalizes : embedded ≤ Subgroup.normalizer (intersection : Set GroupType) := by
        have mapped_le := Subgroup.map_mono (f := target.subtype) internal_normalizes
        have formula := normalizer_subtype_map target (intersection.subgroupOf target)
        rw [Subgroup.map_subgroupOf_eq_of_le intersection_le] at formula
        rw [formula] at mapped_le
        exact mapped_le.trans inf_le_right
      have embedded_factor_normalizes : embedded ≤ Subgroup.normalizer (factor : Set GroupType) :=
        (le_inf embedded_parent embedded_normalizes).trans trap.2
      have embedded_factor : embedded ≤ factor := by
        rw [← parentSylow_embedded]
        apply parent_sylow_normalizer_pgroup_le groupPrime parent parentSylow embedded embedded_parent
          (internal_prime.map target.subtype)
        rwa [parentSylow_embedded]
      have embedded_intersection : embedded ≤ intersection := le_inf embedded_le embedded_factor
      intro element member
      exact embedded_intersection (Subgroup.mem_map_of_mem target.subtype member))
  refine ⟨sylow, sylow_eq.trans ?_⟩
  ext element
  exact and_iff_right element.property

end CFSG.SignalizerFunctor.Helpers
