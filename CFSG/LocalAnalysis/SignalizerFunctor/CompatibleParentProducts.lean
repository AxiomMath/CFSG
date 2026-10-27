module

public import CFSG.LocalAnalysis.SignalizerFunctor.ProductFixedPoints
public import CFSG.LocalAnalysis.SignalizerFunctor.MinimalIncompleteSolvable
public import CFSG.LocalAnalysis.SignalizerFunctor.SubgroupProductCardinality

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem compatible_parent_product_coprime
    (prime rank : ℕ) (prime_prime : prime.Prime) (actor parent : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) (large : prime ^ rank ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (coprime : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values selected)))
    (first second : Subgroup GroupType)
    (first_compatible : signalizerCompatible prime rank actor values first)
    (second_compatible : signalizerCompatible prime rank actor values second)
    (whole : subgroupProduct first second = (parent : Set GroupType)) :
    Nat.Coprime prime (Nat.card parent) := by
  have first_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary large values
    coprime first first_compatible.1 first_compatible.2
  have second_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary large values
    coprime second second_compatible.1 second_compatible.2
  have cardinality := subgroup_product_cardinality first second
  rw [whole] at cardinality
  apply prime_prime.coprime_iff_not_dvd.mpr
  intro divides
  have product_divides : prime ∣ Nat.card first * Nat.card second := by
    rw [cardinality]
    exact dvd_mul_of_dvd_left divides _
  exact (prime_prime.not_dvd_mul (prime_prime.coprime_iff_not_dvd.mp first_coprime)
    (prime_prime.coprime_iff_not_dvd.mp second_coprime)) product_divides

theorem compatible_parent_product_full_centralizers
    (prime rank : ℕ) (prime_prime : prime.Prime) (actor parent : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) (large : prime ^ rank ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (central : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected ≤ Subgroup.centralizer (selected : Set GroupType))
    (coprime : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values selected)))
    (first second : Subgroup GroupType)
    (first_compatible : signalizerCompatible prime rank actor values first)
    (second_compatible : signalizerCompatible prime rank actor values second)
    (whole : subgroupProduct first second = (parent : Set GroupType)) :
    ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected ⊓ parent = parent ⊓ Subgroup.centralizer (selected : Set GroupType) := by
  let _ambientAction := ambientConjugationAction actor
  let _ambientBaseAction : MulAction actor GroupType := _ambientAction.toMulAction
  have first_invariant : ∀ actorElement : actor, ∀ element ∈ first, actorElement • element ∈ first := by
    intro actorElement element member
    exact Subgroup.le_normalizer_iff.mp first_compatible.1 actorElement.val actorElement.property element member
  have second_invariant : ∀ actorElement : actor, ∀ element ∈ second, actorElement • element ∈ second := by
    intro actorElement element member
    exact Subgroup.le_normalizer_iff.mp second_compatible.1 actorElement.val actorElement.property element member
  have first_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary large values
    coprime first first_compatible.1 first_compatible.2
  intro selected member
  apply le_antisymm (le_inf inf_le_right (inf_le_left.trans (central selected member)))
  intro element fixed
  let internalActor := selected.subgroupOf actor
  let _internalAction : MulDistribMulAction internalActor GroupType :=
    MulDistribMulAction.compHom GroupType internalActor.subtype
  let _internalBaseAction : MulAction internalActor GroupType := _internalAction.toMulAction
  have internal_pgroup : IsPGroup prime internalActor :=
    (elementary_abelian_isPGroup prime selected (elementary_abelian_of_le prime elementary member.1)).of_equiv
      (Subgroup.subgroupOfEquivOfLe member.1).symm
  have internal_fixed : ∀ actorElement : internalActor, actorElement • element = element := by
    intro actorElement
    change actorElement.val.val * element * actorElement.val.val⁻¹ = element
    exact mul_inv_eq_iff_eq_mul.mpr
      (Subgroup.mem_centralizer_iff.mp fixed.2 actorElement.val.val actorElement.property)
  have decomposition : ∃ firstElement ∈ first, ∃ secondElement ∈ second,
      firstElement * secondElement = element := by
    change element ∈ subgroupProduct first second
    rw [whole]
    exact fixed.1
  obtain ⟨firstElement, first_member, secondElement, second_member, product, first_fixed, second_fixed⟩ :=
    fixed_product_decomposition prime prime_prime internalActor internal_pgroup GroupType first second
      (fun actorElement => first_invariant actorElement.val)
      (fun actorElement => second_invariant actorElement.val)
      (first_coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)) element internal_fixed decomposition
  have first_central : firstElement ∈ Subgroup.centralizer (selected : Set GroupType) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro actorElement actor_member
    have equality := first_fixed (⟨⟨actorElement, member.1 actor_member⟩, actor_member⟩ : internalActor)
    change actorElement * firstElement * actorElement⁻¹ = firstElement at equality
    exact mul_inv_eq_iff_eq_mul.mp equality
  have second_central : secondElement ∈ Subgroup.centralizer (selected : Set GroupType) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro actorElement actor_member
    have equality := second_fixed (⟨⟨actorElement, member.1 actor_member⟩, actor_member⟩ : internalActor)
    change actorElement * secondElement * actorElement⁻¹ = secondElement at equality
    exact mul_inv_eq_iff_eq_mul.mp equality
  refine ⟨?_, fixed.1⟩
  rw [← product]
  exact (values selected).mul_mem (first_compatible.2 selected member ⟨first_member, first_central⟩)
    (second_compatible.2 selected member ⟨second_member, second_central⟩)

theorem full_parent_centralizers_restriction_completion
    (prime rank : ℕ) (prime_prime : prime.Prime) (actor parent target : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType) (coprime : Nat.Coprime prime (Nat.card parent))
    (target_le : target ≤ parent) (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (full : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected ⊓ parent = parent ⊓ Subgroup.centralizer (selected : Set GroupType)) :
    (⨆ selected ∈ signalizerFunctorEk prime rank actor, signalizerRestriction values target selected) = target := by
  have formula := elementary_abelian_centralizer_generation prime rank prime_prime actor target elementary large
    normalized (coprime.of_dvd_right (Subgroup.card_dvd_of_le target_le))
  have equal := signalizer_completion_congr_values prime rank actor (signalizerRestriction values target)
    (fun selected => target ⊓ Subgroup.centralizer (selected : Set GroupType)) (fun selected member => by
      change values selected ⊓ target = _
      calc
        _ = (values selected ⊓ parent) ⊓ target := by rw [inf_assoc, inf_eq_right.mpr target_le]
        _ = (parent ⊓ Subgroup.centralizer (selected : Set GroupType)) ⊓ target := by rw [full selected member]
        _ = _ := by rw [inf_right_comm, inf_eq_right.mpr target_le])
  exact equal.trans formula

theorem full_parent_centralizers_locally_complete_normalizer_solvable
    (prime rank : ℕ) (prime_prime : prime.Prime) (actor parent target : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType) (coprime : Nat.Coprime prime (Nat.card parent))
    (parent_normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (full : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected ⊓ parent = parent ⊓ Subgroup.centralizer (selected : Set GroupType))
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (compatible : solvableSignalizerCompatible prime rank actor values target) (nontrivial : target ≠ ⊥) :
    solvableSignalizerCompatible prime rank actor values
      (parent ⊓ Subgroup.normalizer (target : Set GroupType)) := by
  let parentNormalizer := parent ⊓ Subgroup.normalizer (target : Set GroupType)
  have normalized : actor ≤ Subgroup.normalizer (parentNormalizer : Set GroupType) :=
    normalizer_inf_of_le actor _ _ parent_normalized (normalizer_normalized actor target compatible.1.1)
  have completion := locally_complete.1 target nontrivial compatible
  have contained : parentNormalizer ≤
      ⨆ selected ∈ signalizerFunctorEk prime rank actor,
        signalizerRestriction values (Subgroup.normalizer (target : Set GroupType)) selected := by
    rw [← full_parent_centralizers_restriction_completion prime rank prime_prime actor parent parentNormalizer
      elementary large values coprime inf_le_left normalized full]
    apply iSup_le
    intro selected
    apply iSup_le
    intro member
    exact (inf_le_inf_left _ inf_le_right).trans
      (signalizer_value_le_completion prime rank actor
        (signalizerRestriction values (Subgroup.normalizer (target : Set GroupType))) member)
  exact solvable_signalizer_compatible_of_le prime rank actor values _ parentNormalizer completion contained normalized

theorem incomplete_full_parent_centralizers_normal_compatible_trivial
    (prime rank : ℕ) (prime_prime : prime.Prime) (actor parent target : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType) (coprime : Nat.Coprime prime (Nat.card parent))
    (parent_normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (full : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected ⊓ parent = parent ⊓ Subgroup.centralizer (selected : Set GroupType))
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (incomplete : ¬ solvableSignalizerCompatible prime rank actor values parent)
    (compatible : solvableSignalizerCompatible prime rank actor values target)
    (target_le : target ≤ parent) (normal : (target.subgroupOf parent).Normal) : target = ⊥ := by
  by_contra nontrivial
  have normalizes := (Subgroup.normal_subgroupOf_iff_le_normalizer target_le).mp normal
  have complete := full_parent_centralizers_locally_complete_normalizer_solvable prime rank prime_prime actor
    parent target elementary large values coprime parent_normalized full locally_complete compatible nontrivial
  rw [inf_eq_left.mpr normalizes] at complete
  exact incomplete complete

end CFSG.SignalizerFunctor.Helpers
