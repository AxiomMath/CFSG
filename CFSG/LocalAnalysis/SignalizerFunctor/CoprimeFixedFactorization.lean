module

public import CFSG.LocalAnalysis.SignalizerFunctor.SylowFixedFactorization

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [CommGroup ActorType] [Finite ActorType]
variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable [MulDistribMulAction ActorType GroupType]

theorem coprime_order_fixed_factorization
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (exponent : ∀ element : ActorType, element ^ prime = 1)
    (large : prime ^ (rank + 1) ≤ Nat.card ActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType))
    (first second : Subgroup GroupType)
    (first_invariant : ∀ actorElement : ActorType, ∀ element ∈ first, actorElement • element ∈ first)
    (second_invariant : ∀ actorElement : ActorType, ∀ element ∈ second, actorElement • element ∈ second)
    (first_normalized : FixedPoints.subgroup ActorType GroupType ≤ Subgroup.normalizer (first : Set GroupType))
    (local_factorization : ∀ actorSubgroup : Subgroup ActorType, Nat.card actorSubgroup = prime ^ rank →
      ∀ element ∈ FixedPoints.subgroup actorSubgroup GroupType,
        ∃ firstElement ∈ first ⊓ FixedPoints.subgroup actorSubgroup GroupType,
          ∃ secondElement ∈ second ⊓ FixedPoints.subgroup actorSubgroup GroupType,
            firstElement * secondElement = element) :
    subgroupProduct first second = Set.univ := by
  classical
  have prime_formula : ∀ groupPrime : ℕ, groupPrime.Prime →
      groupPrime ^ (Nat.card first).factorization groupPrime *
        groupPrime ^ (Nat.card second).factorization groupPrime =
          groupPrime ^ (Nat.card GroupType).factorization groupPrime *
            groupPrime ^ (Nat.card (first ⊓ second : Subgroup GroupType)).factorization groupPrime := by
    intro groupPrime groupPrime_prime
    let : Fact groupPrime.Prime := ⟨groupPrime_prime⟩
    obtain ⟨sylow, first_card, second_card, intersection_card, product_eq⟩ := coprime_sylow_order_fixed_factorization
      prime rank groupPrime prime_prime groupPrime_prime exponent large coprime first second first_invariant
      second_invariant first_normalized local_factorization
    have whole : ∀ element ∈ (sylow : Subgroup GroupType),
        ∃ firstElement ∈ (sylow : Subgroup GroupType) ⊓ first,
          ∃ secondElement ∈ (sylow : Subgroup GroupType) ⊓ second,
            firstElement * secondElement = element :=
      (subgroup_product_eq_subgroup_iff (sylow : Subgroup GroupType) _ _ inf_le_left inf_le_left).mp product_eq
    have cardinality := subgroup_product_cardinality_of_subgroup_whole (sylow : Subgroup GroupType)
      ((sylow : Subgroup GroupType) ⊓ first) ((sylow : Subgroup GroupType) ⊓ second)
      inf_le_left inf_le_left whole
    have intersection_eq : ((sylow : Subgroup GroupType) ⊓ first) ⊓
        ((sylow : Subgroup GroupType) ⊓ second) = ((sylow : Subgroup GroupType) ⊓ first) ⊓ second := by
      ext element
      constructor
      · exact fun member => ⟨member.1, member.2.2⟩
      · exact fun member => ⟨member.1, member.1.1, member.2⟩
    rw [first_card, second_card, intersection_eq, intersection_card, sylow.card_eq_multiplicity] at cardinality
    exact cardinality
  have product_nonempty : Nonempty (subgroupProduct first second) :=
    ⟨⟨1, 1, first.one_mem, 1, second.one_mem, one_mul 1⟩⟩
  let := product_nonempty
  have product_positive : 0 < Nat.card (subgroupProduct first second) := Nat.card_pos
  have cardinality := subgroup_product_cardinality first second
  have factor_cardinality := congrArg (fun order : ℕ => order.factorization) cardinality
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Nat.factorization_mul product_positive.ne' Nat.card_pos.ne'] at factor_cardinality
  have divisible : Nat.card GroupType ∣ Nat.card (subgroupProduct first second) := by
    apply (Nat.factorization_le_iff_dvd Nat.card_pos.ne' product_positive.ne').mp
    intro groupPrime
    by_cases groupPrime_prime : groupPrime.Prime
    · have part_eq := prime_formula groupPrime groupPrime_prime
      rw [← pow_add, ← pow_add] at part_eq
      have exponent_eq := Nat.pow_right_injective groupPrime_prime.two_le part_eq
      have factor_eq := congrArg (fun factors : ℕ →₀ ℕ => factors groupPrime) factor_cardinality
      simp only [Finsupp.add_apply] at factor_eq
      omega
    · rw [Nat.factorization_eq_zero_of_not_prime _ groupPrime_prime]
      exact Nat.zero_le _
  have product_le : Nat.card (subgroupProduct first second) ≤ Nat.card GroupType :=
    Nat.card_le_card_of_injective (fun element : subgroupProduct first second => element.val) Subtype.val_injective
  have card_eq : Nat.card (subgroupProduct first second) = Nat.card GroupType :=
    Nat.le_antisymm product_le (Nat.le_of_dvd product_positive divisible)
  let _productFintype := Fintype.ofFinite (subgroupProduct first second)
  let _univFintype := Fintype.ofFinite (Set.univ : Set GroupType)
  apply Set.eq_of_subset_of_card_le (Set.subset_univ _)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_univ]
  exact card_eq.symm.le

theorem coprime_fixed_factorization
    (prime : ℕ) (prime_prime : prime.Prime)
    (exponent : ∀ element : ActorType, element ^ prime = 1)
    (large : prime ^ 2 ≤ Nat.card ActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType))
    (first second : Subgroup GroupType)
    (first_invariant : ∀ actorElement : ActorType, ∀ element ∈ first, actorElement • element ∈ first)
    (second_invariant : ∀ actorElement : ActorType, ∀ element ∈ second, actorElement • element ∈ second)
    (first_normalized : FixedPoints.subgroup ActorType GroupType ≤ Subgroup.normalizer (first : Set GroupType))
    (local_factorization : ∀ actorSubgroup : Subgroup ActorType, Nat.card actorSubgroup = prime →
      ∀ element ∈ FixedPoints.subgroup actorSubgroup GroupType,
        ∃ firstElement ∈ first ⊓ FixedPoints.subgroup actorSubgroup GroupType,
          ∃ secondElement ∈ second ⊓ FixedPoints.subgroup actorSubgroup GroupType,
            firstElement * secondElement = element) :
    subgroupProduct first second = Set.univ := by
  exact coprime_order_fixed_factorization prime 1 prime_prime exponent large coprime first second
    first_invariant second_invariant first_normalized (by simpa only [pow_one] using local_factorization)

end CFSG.SignalizerFunctor.Helpers
