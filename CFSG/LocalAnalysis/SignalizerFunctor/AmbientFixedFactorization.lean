module

public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowSupplements
public import CFSG.LocalAnalysis.SignalizerFunctor.CoprimeFixedFactorization

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem ambient_order_fixed_factorization
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor parent first second : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (parent_normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card parent))
    (first_le : first ≤ parent) (second_le : second ≤ parent)
    (first_normalized : actor ≤ Subgroup.normalizer (first : Set GroupType))
    (second_normalized : actor ≤ Subgroup.normalizer (second : Set GroupType))
    (fixed_normalized : parent ⊓ Subgroup.centralizer (actor : Set GroupType) ≤
      Subgroup.normalizer (first : Set GroupType))
    (local_factorization : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      ∀ element ∈ parent ⊓ Subgroup.centralizer (selected : Set GroupType),
        ∃ firstElement ∈ first ⊓ Subgroup.centralizer (selected : Set GroupType),
          ∃ secondElement ∈ second ⊓ Subgroup.centralizer (selected : Set GroupType),
            firstElement * secondElement = element) :
    subgroupProduct first second = (parent : Set GroupType) := by
  let := elementary.1
  let _actorCommGroup : CommGroup actor := { actor.toGroup with mul_comm := mul_comm' }
  let _parentAction := conjugationAction actor parent parent_normalized
  have exponent : ∀ element : actor, element ^ prime = 1 := by
    intro element
    exact Subtype.ext (elementary.2 element.val element.property)
  have left_invariant := normalized_subgroup_invariant_subgroup actor parent first parent_normalized first_normalized
  have right_invariant := normalized_subgroup_invariant_subgroup actor parent second parent_normalized second_normalized
  have internal_fixed_normalized : FixedPoints.subgroup actor parent ≤
      Subgroup.normalizer (first.subgroupOf parent : Set parent) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro conjugator fixed element member
    have ambient_fixed : conjugator.val ∈ parent ⊓ Subgroup.centralizer (actor : Set GroupType) := by
      have fixed_member := Subgroup.mem_map_of_mem parent.subtype fixed
      rw [conjugation_fixed_subgroup_map actor parent parent_normalized] at fixed_member
      exact fixed_member
    exact Subgroup.le_normalizer_iff.mp fixed_normalized conjugator.val ambient_fixed element.val member
  have internal_local : ∀ selected : Subgroup actor, Nat.card selected = prime ^ rank →
      ∀ element ∈ FixedPoints.subgroup selected parent,
        ∃ leftElement ∈ first.subgroupOf parent ⊓ FixedPoints.subgroup selected parent,
          ∃ rightElement ∈ second.subgroupOf parent ⊓ FixedPoints.subgroup selected parent,
            leftElement * rightElement = element := by
    intro selected cardinality element fixed
    let embedded := selected.map actor.subtype
    have embedded_member : embedded ∈ signalizerFunctorEk prime rank actor :=
      ⟨Subgroup.map_subtype_le _, by rwa [Subgroup.card_map_of_injective actor.subtype_injective]⟩
    have ambient_fixed : element.val ∈ parent ⊓ Subgroup.centralizer (embedded : Set GroupType) := by
      refine ⟨element.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro actorElement ⟨original, member, rfl⟩
      have equality := congrArg Subtype.val (fixed (⟨original, member⟩ : selected))
      change original.val * element.val * original.val⁻¹ = element.val at equality
      exact mul_inv_eq_iff_eq_mul.mp equality
    obtain ⟨leftElement, left_member, rightElement, right_member, product⟩ :=
      local_factorization embedded embedded_member element.val ambient_fixed
    refine ⟨⟨leftElement, first_le left_member.1⟩, ⟨left_member.1, ?_⟩,
      ⟨rightElement, second_le right_member.1⟩, ⟨right_member.1, ?_⟩, Subtype.ext product⟩
    · intro actorElement
      apply Subtype.ext
      change actorElement.val.val * leftElement * actorElement.val.val⁻¹ = leftElement
      exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp left_member.2 actorElement.val.val
        (Subgroup.mem_map_of_mem actor.subtype actorElement.property))
    · intro actorElement
      apply Subtype.ext
      change actorElement.val.val * rightElement * actorElement.val.val⁻¹ = rightElement
      exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp right_member.2 actorElement.val.val
        (Subgroup.mem_map_of_mem actor.subtype actorElement.property))
  have internal_factorization := coprime_order_fixed_factorization prime rank prime_prime exponent large coprime
    (first.subgroupOf parent) (second.subgroupOf parent) left_invariant right_invariant
    internal_fixed_normalized internal_local
  have decomposable := (subgroup_product_eq_univ_iff _ _).mp internal_factorization
  apply (subgroup_product_eq_subgroup_iff parent first second first_le second_le).mpr
  intro element member
  obtain ⟨leftElement, left_member, rightElement, right_member, product⟩ := decomposable ⟨element, member⟩
  exact ⟨leftElement.val, left_member, rightElement.val, right_member, congrArg Subtype.val product⟩

end CFSG.SignalizerFunctor.Helpers
