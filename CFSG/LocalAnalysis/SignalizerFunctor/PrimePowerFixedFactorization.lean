module

public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerConditions
public import CFSG.LocalAnalysis.SignalizerFunctor.FixedPointImages

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [CommGroup ActorType] [Finite ActorType]
variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable [MulDistribMulAction ActorType GroupType]

omit [Finite ActorType] [Finite GroupType] in
theorem subgroup_center_invariant :
    ∀ actorElement : ActorType, ∀ element ∈ Subgroup.center GroupType,
      actorElement • element ∈ Subgroup.center GroupType := by
  intro actorElement element member
  exact Subgroup.characteristic_iff_le_comap.mp inferInstance
    (MulDistribMulAction.toMulEquiv GroupType actorElement) member

omit [Finite ActorType] [Finite GroupType] in
theorem fixed_subgroup_invariant_of_commutative_actor (actorSubgroup : Subgroup ActorType) :
    ∀ actorElement : ActorType, ∀ element ∈ FixedPoints.subgroup actorSubgroup GroupType,
      actorElement • element ∈ FixedPoints.subgroup actorSubgroup GroupType := by
  intro actorElement element fixed fixedElement
  have fixed_eq : fixedElement.val • element = element := fixed fixedElement
  change fixedElement.val • (actorElement • element) = actorElement • element
  rw [← mul_smul, mul_comm fixedElement.val actorElement, mul_smul, fixed_eq]

omit [Finite GroupType] in
theorem central_subgroup_normal (subgroup : Subgroup GroupType)
    (central : subgroup ≤ Subgroup.center GroupType) : subgroup.Normal := by
  refine ⟨?_⟩
  intro element member conjugator
  rw [Subgroup.mem_center_iff.mp (central member) conjugator, mul_assoc, mul_inv_cancel, mul_one]
  exact member

theorem nontrivial_fixed_center_subgroup_order (prime rank groupPrime : ℕ)
    (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (exponent : ∀ element : ActorType, element ^ prime = 1)
    (large : prime ^ (rank + 1) ≤ Nat.card ActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType))
    (pgroup : IsPGroup groupPrime GroupType) [Nontrivial GroupType] :
    ∃ actorSubgroup : Subgroup ActorType, Nat.card actorSubgroup = prime ^ rank ∧
      Subgroup.center GroupType ⊓ FixedPoints.subgroup actorSubgroup GroupType ≠ ⊥ := by
  let : Fact groupPrime.Prime := ⟨groupPrime_prime⟩
  let center := Subgroup.center GroupType
  let _nontrivialCenter := pgroup.center_nontrivial
  have center_invariant := subgroup_center_invariant (ActorType := ActorType) (GroupType := GroupType)
  let _centerAction := invariantSubgroupAction center center_invariant
  have center_coprime := coprime.of_dvd_right center.card_subgroup_dvd_card
  have generated := elementary_abelian_order_generation prime rank prime_prime ActorType exponent
    large center center_coprime
  have mapped_generated := congrArg (Subgroup.map center.subtype) generated
  rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, center.subtype_range] at mapped_generated
  simp_rw [Subgroup.map_iSup] at mapped_generated
  have mapped_fixed : ∀ actorSubgroup : Subgroup ActorType,
      (FixedPoints.subgroup actorSubgroup center).map center.subtype =
        center ⊓ FixedPoints.subgroup actorSubgroup GroupType := by
    intro actorSubgroup
    exact invariant_subgroup_fixed_points_map center
      (fun actorElement : actorSubgroup => center_invariant actorElement.val)
  simp_rw [mapped_fixed] at mapped_generated
  by_contra none
  push Not at none
  have trivial : (⨆ actorSubgroup : Subgroup ActorType,
      ⨆ (_ : Nat.card actorSubgroup = prime ^ rank),
        center ⊓ FixedPoints.subgroup actorSubgroup GroupType) = ⊥ := by
    apply iSup_eq_bot.mpr
    intro actorSubgroup
    apply iSup_eq_bot.mpr
    intro cardinality
    exact none actorSubgroup cardinality
  rw [trivial] at mapped_generated
  exact (Subgroup.nontrivial_iff_ne_bot center).mp inferInstance mapped_generated.symm

theorem prime_power_order_fixed_factorization
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (exponent : ∀ element : ActorType, element ^ prime = 1)
    (large : prime ^ (rank + 1) ≤ Nat.card ActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType)) (pgroup : IsPGroup groupPrime GroupType)
    (first second : Subgroup GroupType)
    (first_invariant : ∀ actorElement : ActorType, ∀ element ∈ first, actorElement • element ∈ first)
    (second_invariant : ∀ actorElement : ActorType, ∀ element ∈ second, actorElement • element ∈ second)
    (first_fixed_normalized : FixedPoints.subgroup ActorType GroupType ≤
      Subgroup.normalizer (first : Set GroupType))
    (local_factorization : ∀ actorSubgroup : Subgroup ActorType, Nat.card actorSubgroup = prime ^ rank →
      ∀ element ∈ FixedPoints.subgroup actorSubgroup GroupType,
        ∃ firstElement ∈ first ⊓ FixedPoints.subgroup actorSubgroup GroupType,
          ∃ secondElement ∈ second ⊓ FixedPoints.subgroup actorSubgroup GroupType,
            firstElement * secondElement = element) :
    ∀ element : GroupType, ∃ firstElement ∈ first, ∃ secondElement ∈ second,
      firstElement * secondElement = element := by
  suffices general : ∀ order : ℕ,
      ∀ (TargetType : Type groupUniverse) [Group TargetType] [Finite TargetType]
        [MulDistribMulAction ActorType TargetType], Nat.card TargetType = order →
        Nat.Coprime prime (Nat.card TargetType) → IsPGroup groupPrime TargetType →
        ∀ (left right : Subgroup TargetType),
          (∀ actorElement : ActorType, ∀ element ∈ left, actorElement • element ∈ left) →
          (∀ actorElement : ActorType, ∀ element ∈ right, actorElement • element ∈ right) →
          FixedPoints.subgroup ActorType TargetType ≤ Subgroup.normalizer (left : Set TargetType) →
          (∀ actorSubgroup : Subgroup ActorType, Nat.card actorSubgroup = prime ^ rank →
            ∀ element ∈ FixedPoints.subgroup actorSubgroup TargetType,
              ∃ leftElement ∈ left ⊓ FixedPoints.subgroup actorSubgroup TargetType,
                ∃ rightElement ∈ right ⊓ FixedPoints.subgroup actorSubgroup TargetType,
                  leftElement * rightElement = element) →
          ∀ element : TargetType, ∃ leftElement ∈ left, ∃ rightElement ∈ right,
            leftElement * rightElement = element by
    exact general (Nat.card GroupType) GroupType rfl coprime pgroup first second first_invariant
      second_invariant first_fixed_normalized local_factorization
  intro order
  induction order using Nat.strong_induction_on with
  | h order induction_hypothesis =>
    intro TargetType _ _ _ target_card target_coprime target_pgroup left right
      left_invariant right_invariant left_normalized local_products
    rcases subsingleton_or_nontrivial TargetType with trivial | nontrivial
    · let := trivial
      intro element
      exact ⟨1, left.one_mem, 1, right.one_mem, by simp [Subsingleton.elim element 1]⟩
    · let := nontrivial
      obtain ⟨fixedActor, fixedActor_card, normal_nontrivial⟩ := nontrivial_fixed_center_subgroup_order
        prime rank groupPrime prime_prime groupPrime_prime exponent large target_coprime target_pgroup
      let normal := Subgroup.center TargetType ⊓ FixedPoints.subgroup fixedActor TargetType
      have central : normal ≤ Subgroup.center TargetType := inf_le_left
      let _normal := central_subgroup_normal normal central
      have normal_invariant : ∀ actorElement : ActorType, ∀ element ∈ normal,
          actorElement • element ∈ normal := by
        intro actorElement element member
        exact ⟨subgroup_center_invariant actorElement element member.1,
          fixed_subgroup_invariant_of_commutative_actor fixedActor actorElement element member.2⟩
      let _quotientAction := invariantQuotientAction normal normal_invariant
      let projection := QuotientGroup.mk' normal
      have equivariant := invariant_quotient_equivariant normal normal_invariant
      have actor_pgroup : IsPGroup prime ActorType := by
        intro element
        exact ⟨1, by simpa only [pow_one] using exponent element⟩
      have kernel_coprime : Nat.Coprime prime (Nat.card projection.ker) := by
        rw [QuotientGroup.ker_mk']
        exact target_coprime.of_dvd_right normal.card_subgroup_dvd_card
      have quotient_coprime : Nat.Coprime prime (Nat.card (TargetType ⧸ normal)) :=
        target_coprime.of_dvd_right normal.card_quotient_dvd_card
      have quotient_pgroup := target_pgroup.to_quotient normal
      have image_left_invariant := equivariant_subgroup_image_invariant projection equivariant left left_invariant
      have image_right_invariant := equivariant_subgroup_image_invariant projection equivariant right right_invariant
      have image_normalized := fixed_normalized_subgroup_image prime prime_prime actor_pgroup projection
        (QuotientGroup.mk'_surjective normal) equivariant kernel_coprime left left_normalized
      have quotient_products : ∀ actorSubgroup : Subgroup ActorType, Nat.card actorSubgroup = prime ^ rank →
          ∀ element ∈ FixedPoints.subgroup actorSubgroup (TargetType ⧸ normal),
            ∃ leftElement ∈ left.map projection ⊓ FixedPoints.subgroup actorSubgroup (TargetType ⧸ normal),
              ∃ rightElement ∈ right.map projection ⊓ FixedPoints.subgroup actorSubgroup (TargetType ⧸ normal),
                leftElement * rightElement = element := by
        intro actorSubgroup actorSubgroup_card element fixed
        have restricted_equivariant : ∀ actorElement : actorSubgroup, ∀ value : TargetType,
            projection (actorElement • value) = actorElement • projection value := by
          intro actorElement value
          exact equivariant actorElement.val value
        obtain ⟨original, image_eq, original_fixed⟩ := fixed_point_lifts prime prime_prime
          (actor_pgroup.to_subgroup actorSubgroup) projection (QuotientGroup.mk'_surjective normal)
          restricted_equivariant kernel_coprime element fixed
        obtain ⟨leftElement, left_member, rightElement, right_member, product_eq⟩ :=
          local_products actorSubgroup actorSubgroup_card original original_fixed
        refine ⟨projection leftElement, ⟨Subgroup.mem_map_of_mem projection left_member.1, ?_⟩,
          projection rightElement, ⟨Subgroup.mem_map_of_mem projection right_member.1, ?_⟩, ?_⟩
        · intro actorElement
          rw [← restricted_equivariant, left_member.2 actorElement]
        · intro actorElement
          rw [← restricted_equivariant, right_member.2 actorElement]
        · rw [← map_mul, product_eq, image_eq]
      have quotient_smaller : Nat.card (TargetType ⧸ normal) < order := by
        rw [← target_card]
        exact normal_quotient_card_strict normal normal_nontrivial
      have quotient_factorization := induction_hypothesis (Nat.card (TargetType ⧸ normal)) quotient_smaller
        (TargetType ⧸ normal) rfl quotient_coprime quotient_pgroup (left.map projection) (right.map projection)
        image_left_invariant image_right_invariant image_normalized quotient_products
      intro element
      obtain ⟨leftImage, left_image_member, rightImage, right_image_member, image_product⟩ :=
        quotient_factorization (projection element)
      obtain ⟨leftElement, left_member, left_image_eq⟩ := left_image_member
      obtain ⟨rightElement, right_member, right_image_eq⟩ := right_image_member
      have product_image : projection (leftElement * rightElement) = projection element := by
        rw [map_mul, left_image_eq, right_image_eq]
        exact image_product
      let difference := (leftElement * rightElement)⁻¹ * element
      have difference_member : difference ∈ normal := by
        apply (QuotientGroup.eq_one_iff _).mp
        change projection ((leftElement * rightElement)⁻¹ * element) = 1
        rw [map_mul, map_inv, product_image, inv_mul_cancel]
      have reordered : leftElement * difference * rightElement = element := by
        have commutes := Subgroup.mem_center_iff.mp (central difference_member) rightElement
        rw [mul_assoc, ← commutes, ← mul_assoc]
        change (leftElement * rightElement) * ((leftElement * rightElement)⁻¹ * element) = element
        exact mul_inv_cancel_left _ _
      obtain ⟨centralLeft, central_left_member, centralRight, central_right_member, central_product⟩ :=
        local_products fixedActor fixedActor_card difference difference_member.2
      refine ⟨leftElement * centralLeft, left.mul_mem left_member central_left_member.1,
        centralRight * rightElement, right.mul_mem central_right_member.1 right_member, ?_⟩
      rw [mul_assoc, ← mul_assoc centralLeft, central_product, ← mul_assoc]
      exact reordered

theorem nontrivial_fixed_center_subgroup (prime groupPrime : ℕ)
    (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (exponent : ∀ element : ActorType, element ^ prime = 1)
    (large : prime ^ 2 ≤ Nat.card ActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType))
    (pgroup : IsPGroup groupPrime GroupType) [Nontrivial GroupType] :
    ∃ actorSubgroup : Subgroup ActorType, Nat.card actorSubgroup = prime ∧
      Subgroup.center GroupType ⊓ FixedPoints.subgroup actorSubgroup GroupType ≠ ⊥ := by
  simpa only [pow_one] using nontrivial_fixed_center_subgroup_order prime 1 groupPrime
    prime_prime groupPrime_prime exponent large coprime pgroup

theorem prime_power_fixed_factorization
    (prime groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (exponent : ∀ element : ActorType, element ^ prime = 1)
    (large : prime ^ 2 ≤ Nat.card ActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType)) (pgroup : IsPGroup groupPrime GroupType)
    (first second : Subgroup GroupType)
    (first_invariant : ∀ actorElement : ActorType, ∀ element ∈ first, actorElement • element ∈ first)
    (second_invariant : ∀ actorElement : ActorType, ∀ element ∈ second, actorElement • element ∈ second)
    (first_fixed_normalized : FixedPoints.subgroup ActorType GroupType ≤
      Subgroup.normalizer (first : Set GroupType))
    (local_factorization : ∀ actorSubgroup : Subgroup ActorType, Nat.card actorSubgroup = prime →
      ∀ element ∈ FixedPoints.subgroup actorSubgroup GroupType,
        ∃ firstElement ∈ first ⊓ FixedPoints.subgroup actorSubgroup GroupType,
          ∃ secondElement ∈ second ⊓ FixedPoints.subgroup actorSubgroup GroupType,
            firstElement * secondElement = element) :
    ∀ element : GroupType, ∃ firstElement ∈ first, ∃ secondElement ∈ second,
      firstElement * secondElement = element := by
  exact prime_power_order_fixed_factorization prime 1 groupPrime prime_prime groupPrime_prime exponent
    large coprime pgroup first second first_invariant second_invariant first_fixed_normalized
    (by simpa only [pow_one] using local_factorization)

end CFSG.SignalizerFunctor.Helpers
