module

public import CFSG.LocalAnalysis.SignalizerFunctor.ProductFixedPoints
public import CFSG.LocalAnalysis.SignalizerFunctor.MinimalIncompleteSolvable
public import CFSG.LocalAnalysis.SignalizerFunctor.SubgroupProductCardinality

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem compatible_product_coprime
    (prime rank : ℕ) (prime_prime : prime.Prime) (actor : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) (large : prime ^ rank ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (coprime : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values selected)))
    (first second : Subgroup GroupType)
    (first_compatible : signalizerCompatible prime rank actor values first)
    (second_compatible : signalizerCompatible prime rank actor values second)
    (whole : subgroupProduct first second = Set.univ) :
    Nat.Coprime prime (Nat.card GroupType) := by
  have first_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary large values
    coprime first first_compatible.1 first_compatible.2
  have second_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary large values
    coprime second second_compatible.1 second_compatible.2
  have cardinality := subgroup_product_cardinality first second
  rw [whole, Nat.card_univ] at cardinality
  apply prime_prime.coprime_iff_not_dvd.mpr
  intro divides
  have product_divides : prime ∣ Nat.card first * Nat.card second := by
    rw [cardinality]
    exact dvd_mul_of_dvd_left divides _
  exact (prime_prime.not_dvd_mul (prime_prime.coprime_iff_not_dvd.mp first_coprime)
    (prime_prime.coprime_iff_not_dvd.mp second_coprime)) product_divides

theorem compatible_product_full_centralizers
    (prime rank : ℕ) (prime_prime : prime.Prime) (actor : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) (large : prime ^ rank ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (central : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected ≤ Subgroup.centralizer (selected : Set GroupType))
    (coprime : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values selected)))
    (first second : Subgroup GroupType)
    (first_compatible : signalizerCompatible prime rank actor values first)
    (second_compatible : signalizerCompatible prime rank actor values second)
    (whole : subgroupProduct first second = Set.univ) :
    ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected = Subgroup.centralizer (selected : Set GroupType) := by
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
  have decomposable := (subgroup_product_eq_univ_iff first second).mp whole
  intro selected member
  apply le_antisymm (central selected member)
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
      (Subgroup.mem_centralizer_iff.mp fixed actorElement.val.val actorElement.property)
  obtain ⟨firstElement, first_member, secondElement, second_member, product, first_fixed, second_fixed⟩ :=
    fixed_product_decomposition prime prime_prime internalActor internal_pgroup GroupType first second
      (fun actorElement => first_invariant actorElement.val)
      (fun actorElement => second_invariant actorElement.val)
      (first_coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)) element internal_fixed
      (decomposable element)
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
  rw [← product]
  exact (values selected).mul_mem (first_compatible.2 selected member ⟨first_member, first_central⟩)
    (second_compatible.2 selected member ⟨second_member, second_central⟩)

theorem full_centralizers_completion_eq_top
    (prime rank : ℕ) (prime_prime : prime.Prime) (actor : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType) (coprime : Nat.Coprime prime (Nat.card GroupType))
    (full : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected = Subgroup.centralizer (selected : Set GroupType)) :
    (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) = ⊤ := by
  have formula := elementary_abelian_centralizer_generation prime rank prime_prime actor ⊤ elementary large
    (by rw [Subgroup.normalizer_eq_top]; exact le_top) (by rwa [Subgroup.card_top])
  simp only [top_inf_eq] at formula
  exact (signalizer_completion_congr_values prime rank actor values
    (fun selected => Subgroup.centralizer (selected : Set GroupType)) full).trans formula

omit [Finite GroupType] in
theorem full_centralizers_compatible_iff (prime rank : ℕ) (actor target : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (full : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected = Subgroup.centralizer (selected : Set GroupType)) :
    signalizerCompatible prime rank actor values target ↔ actor ≤ Subgroup.normalizer (target : Set GroupType) := by
  constructor
  · exact And.left
  · intro normalized
    refine ⟨normalized, ?_⟩
    intro selected member
    rw [full selected member]
    exact inf_le_right

theorem full_centralizers_restriction_completion
    (prime rank : ℕ) (prime_prime : prime.Prime) (actor ambient : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType) (coprime : Nat.Coprime prime (Nat.card GroupType))
    (normalized : actor ≤ Subgroup.normalizer (ambient : Set GroupType))
    (full : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected = Subgroup.centralizer (selected : Set GroupType)) :
    (⨆ selected ∈ signalizerFunctorEk prime rank actor, signalizerRestriction values ambient selected) = ambient := by
  have formula := elementary_abelian_centralizer_generation prime rank prime_prime actor ambient elementary
    large normalized (coprime.of_dvd_right ambient.card_subgroup_dvd_card)
  have equal := signalizer_completion_congr_values prime rank actor (signalizerRestriction values ambient)
    (fun selected => ambient ⊓ Subgroup.centralizer (selected : Set GroupType))
    (fun selected member => by change values selected ⊓ ambient = _; rw [full selected member, inf_comm])
  exact equal.trans formula

theorem full_centralizers_locally_complete_normalizer_solvable
    (prime rank : ℕ) (prime_prime : prime.Prime) (actor target : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType) (coprime : Nat.Coprime prime (Nat.card GroupType))
    (full : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected = Subgroup.centralizer (selected : Set GroupType))
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (compatible : solvableSignalizerCompatible prime rank actor values target) (nontrivial : target ≠ ⊥) :
    solvableSignalizerCompatible prime rank actor values (Subgroup.normalizer (target : Set GroupType)) := by
  have complete := locally_complete.1 target nontrivial compatible
  have equal := full_centralizers_restriction_completion prime rank prime_prime actor
    (Subgroup.normalizer (target : Set GroupType)) elementary large values coprime
    (normalizer_normalized actor target compatible.1.1) full
  rwa [equal] at complete

end CFSG.SignalizerFunctor.Helpers
