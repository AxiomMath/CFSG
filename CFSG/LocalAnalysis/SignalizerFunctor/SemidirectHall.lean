module

public import CFSG.LocalAnalysis.SignalizerFunctor.HallContainment

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

@[expose] def invariantSemidirectSubgroup
    (ActorType : Type actorUniverse) [Group ActorType]
    (GroupType : Type groupUniverse) [Group GroupType]
    [MulDistribMulAction ActorType GroupType]
    (subgroup : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup,
      actorElement • element ∈ subgroup) :
    Subgroup (GroupType ⋊[MulDistribMulAction.toMulAut ActorType GroupType] ActorType) where
  carrier := {element | element.left ∈ subgroup}
  one_mem' := subgroup.one_mem
  mul_mem' := by
    intro first second first_member second_member
    exact subgroup.mul_mem first_member (invariant first.right second.left second_member)
  inv_mem' := by
    intro element member
    exact invariant element.right⁻¹ element.left⁻¹ (subgroup.inv_mem member)

theorem invariant_semidirect_subgroup_card
    (ActorType : Type actorUniverse) [Group ActorType]
    (GroupType : Type groupUniverse) [Group GroupType]
    [MulDistribMulAction ActorType GroupType]
    (subgroup : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup,
      actorElement • element ∈ subgroup) :
    Nat.card (invariantSemidirectSubgroup ActorType GroupType subgroup invariant) =
      Nat.card subgroup * Nat.card ActorType := by
  let equiv : invariantSemidirectSubgroup ActorType GroupType subgroup invariant ≃
      subgroup × ActorType :=
    { toFun := fun element => (⟨element.val.left, element.property⟩, element.val.right)
      invFun := fun pair => ⟨⟨pair.1.val, pair.2⟩, pair.1.property⟩
      left_inv := fun element => Subtype.ext (SemidirectProduct.ext rfl rfl)
      right_inv := fun _ => rfl }
  rw [Nat.card_congr equiv, Nat.card_prod]

theorem semidirect_subgroup_card_of_inr_le
    (ActorType : Type actorUniverse) [Group ActorType]
    (GroupType : Type groupUniverse) [Group GroupType]
    (action : ActorType →* MulAut GroupType)
    (subgroup : Subgroup (GroupType ⋊[action] ActorType))
    (contains_actor : ∀ actorElement : ActorType, SemidirectProduct.inr actorElement ∈ subgroup) :
    Nat.card subgroup = Nat.card (subgroup.comap SemidirectProduct.inl) * Nat.card ActorType := by
  have left_member : ∀ element ∈ subgroup, SemidirectProduct.inl element.left ∈ subgroup := by
    intro element member
    have product_member := subgroup.mul_mem member (subgroup.inv_mem (contains_actor element.right))
    have equality : element * (SemidirectProduct.inr element.right)⁻¹ =
        SemidirectProduct.inl element.left := by
      rcases element with ⟨left, right⟩
      change (⟨left, right⟩ : GroupType ⋊[action] ActorType) *
        (SemidirectProduct.inr right)⁻¹ = SemidirectProduct.inl left
      rw [SemidirectProduct.mk_eq_inl_mul_inr right left]
      simp only [mul_inv_cancel_right]
    rwa [equality] at product_member
  let equiv : subgroup ≃ subgroup.comap SemidirectProduct.inl × ActorType :=
    { toFun := fun element => (⟨element.val.left, left_member element.val element.property⟩,
        element.val.right)
      invFun := fun pair => ⟨⟨pair.1.val, pair.2⟩, by
        rw [SemidirectProduct.mk_eq_inl_mul_inr]
        exact subgroup.mul_mem pair.1.property (contains_actor pair.2)⟩
      left_inv := fun element => Subtype.ext (SemidirectProduct.ext rfl rfl)
      right_inv := fun _ => rfl }
  rw [Nat.card_congr equiv, Nat.card_prod]

theorem solvable_semidirect_product
    (ActorType : Type actorUniverse) [Group ActorType] [Group.IsSolvable ActorType]
    (GroupType : Type groupUniverse) [Group GroupType] [Group.IsSolvable GroupType]
    (action : ActorType →* MulAut GroupType) : Group.IsSolvable (GroupType ⋊[action] ActorType) := by
  apply Group.isSolvable_of_ker_le_range SemidirectProduct.inl SemidirectProduct.rightHom
  intro element member
  refine ⟨element.left, ?_⟩
  apply SemidirectProduct.ext
  · exact SemidirectProduct.left_inl _
  · exact member.symm

theorem invariant_hall_subgroup_containing
    (prime : ℕ) (prime_prime : prime.Prime)
    (ActorType : Type actorUniverse) [Group ActorType] [Finite ActorType]
    (actor_pgroup : IsPGroup prime ActorType)
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType]
    [Group.IsSolvable GroupType] [MulDistribMulAction ActorType GroupType]
    (coprime : Nat.Coprime prime (Nat.card GroupType))
    (primes : Set ℕ)
    (subgroup : Subgroup GroupType) (supported : primeSupported primes (Nat.card subgroup))
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup,
      actorElement • element ∈ subgroup) :
    ∃ hall : Subgroup GroupType, subgroup ≤ hall ∧ IsHallSubgroup primes hall ∧
      ∀ actorElement : ActorType, ∀ element ∈ hall, actorElement • element ∈ hall := by
  classical
  let : Fact prime.Prime := ⟨prime_prime⟩
  let _actorNilpotent : Group.IsNilpotent ActorType := actor_pgroup.isNilpotent
  let action := MulDistribMulAction.toMulAut ActorType GroupType
  let semidirect := GroupType ⋊[action] ActorType
  let : Finite semidirect := Finite.of_equiv (GroupType × ActorType) SemidirectProduct.equivProd.symm
  let _solvable : Group.IsSolvable semidirect :=
    solvable_semidirect_product ActorType GroupType action
  let enlargedPrimes : Set ℕ := primes ∪ {prime}
  let embedded := invariantSemidirectSubgroup ActorType GroupType subgroup invariant
  have embedded_supported : primeSupported enlargedPrimes (Nat.card embedded) := by
    rw [invariant_semidirect_subgroup_card]
    apply prime_supported_mul
    · intro divisor divisor_prime divides
      exact Or.inl (supported divisor divisor_prime divides)
    · obtain ⟨rank, cardinality⟩ := IsPGroup.iff_card.mp actor_pgroup
      rw [cardinality]
      exact prime_supported_pow_prime enlargedPrimes prime rank prime_prime (Or.inr rfl)
  obtain ⟨overgroup, contains, overgroup_hall⟩ := solvable_hall_subgroup_containing semidirect
    enlargedPrimes embedded embedded_supported
  have contains_actor : ∀ actorElement : ActorType, SemidirectProduct.inr actorElement ∈ overgroup :=
    fun _ => contains subgroup.one_mem
  let hall := overgroup.comap (SemidirectProduct.inl (φ := action))
  have hall_contains : subgroup ≤ hall := by
    intro element member
    exact contains member
  have hall_supported : primeSupported primes (Nat.card hall) := by
    intro divisor divisor_prime divides
    have overgroup_divides := divides.trans
      (Subgroup.card_comap_dvd_of_injective overgroup SemidirectProduct.inl
        SemidirectProduct.inl_injective)
    rcases overgroup_hall.1 divisor divisor_prime overgroup_divides with member | equal
    · exact member
    · have equal_prime : divisor = prime := equal
      have group_divides := divides.trans (Subgroup.card_subgroup_dvd_card hall)
      rw [equal_prime] at group_divides
      exact ((prime_prime.coprime_iff_not_dvd.mp coprime) group_divides).elim
  have index_equal : hall.index = overgroup.index := by
    have overgroup_card := semidirect_subgroup_card_of_inr_le ActorType GroupType action
      overgroup contains_actor
    have overgroup_product := overgroup.card_mul_index
    have hall_product := hall.card_mul_index
    change Nat.card overgroup = Nat.card hall * Nat.card ActorType at overgroup_card
    rw [overgroup_card, SemidirectProduct.card] at overgroup_product
    nlinarith [Nat.card_pos (α := ActorType), Nat.card_pos (α := hall)]
  have index_supported : primeSupported primesᶜ hall.index := by
    rw [index_equal]
    intro divisor divisor_prime divides member
    exact overgroup_hall.2 divisor divisor_prime divides (Or.inl member)
  refine ⟨hall, hall_contains, ⟨hall_supported, index_supported⟩, ?_⟩
  intro actorElement element member
  change SemidirectProduct.inl (actorElement • element) ∈ overgroup
  rw [show actorElement • element = action actorElement element from rfl,
    SemidirectProduct.inl_aut]
  exact overgroup.mul_mem (overgroup.mul_mem (contains_actor actorElement) member)
    (contains_actor actorElement⁻¹)

end CFSG.SignalizerFunctor.Helpers
