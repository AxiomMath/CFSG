module

public import CFSG.LocalAnalysis.SignalizerFunctor.IncompleteHallProduct
public import CFSG.LocalAnalysis.SignalizerFunctor.MatsuyamaWeakClosure

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem subgroup_product_replace_contained_factor (parent core control first second : Subgroup GroupType)
    (core_le : core ≤ parent) (control_le : control ≤ parent)
    (first_le : first ≤ core) (second_le : second ≤ control)
    (whole : subgroupProduct core control = (parent : Set GroupType))
    (core_product : subgroupProduct first second = (core : Set GroupType)) :
    subgroupProduct first control = (parent : Set GroupType) := by
  apply (subgroup_product_eq_subgroup_iff parent first control (first_le.trans core_le) control_le).mpr
  intro element member
  obtain ⟨coreElement, core_member, controlElement, control_member, product⟩ :=
    (subgroup_product_eq_subgroup_iff parent core control core_le control_le).mp whole element member
  obtain ⟨firstElement, first_member, secondElement, second_member, core_equal⟩ :=
    (subgroup_product_eq_subgroup_iff core first second first_le
      (by
        intro candidate candidate_member
        have product_member : candidate ∈ subgroupProduct first second :=
          ⟨1, first.one_mem, candidate, candidate_member, one_mul candidate⟩
        rwa [core_product] at product_member)).mp core_product coreElement core_member
  refine ⟨firstElement, first_member, secondElement * controlElement,
    control.mul_mem (second_le second_member) control_member, ?_⟩
  rw [← mul_assoc, core_equal, product]

theorem normalized_orbit_le_of_product (actor target bound first second : Subgroup GroupType)
    (whole : subgroupProduct first second = (actor : Set GroupType))
    (first_le : first ≤ bound) (target_le : target ≤ bound)
    (second_normalized : second ≤ Subgroup.normalizer (target : Set GroupType)) :
    normalizedConjugateHull actor target ≤ bound := by
  apply iSup_le
  intro actorElement
  obtain ⟨firstElement, first_member, secondElement, second_member, product⟩ :=
    (show actorElement.val ∈ subgroupProduct first second from whole.symm ▸ actorElement.property)
  intro element member
  obtain ⟨original, original_member, image⟩ := member
  change actorElement.val * original * actorElement.val⁻¹ = element at image
  rw [← image, ← product]
  have normalized := Subgroup.le_normalizer_iff.mp second_normalized secondElement second_member
    original original_member
  have equal : (firstElement * secondElement) * original * (firstElement * secondElement)⁻¹ =
      firstElement * (secondElement * original * secondElement⁻¹) * firstElement⁻¹ := by group
  rw [equal]
  exact bound.mul_mem (bound.mul_mem (first_le first_member) (target_le normalized))
    (bound.inv_mem (first_le first_member))

theorem normalized_conjugate_hull_external_normalized (external actor target : Subgroup GroupType)
    (actor_normalized : external ≤ Subgroup.normalizer (actor : Set GroupType))
    (target_normalized : external ≤ Subgroup.normalizer (target : Set GroupType)) :
    external ≤ Subgroup.normalizer (normalizedConjugateHull actor target : Set GroupType) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator conjugator_member element member
  have image_le : (normalizedConjugateHull actor target).map (MulAut.conj conjugator).toMonoidHom ≤
      normalizedConjugateHull actor target := by
    unfold normalizedConjugateHull
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro actorElement
    change conjugateSubgroup conjugator (conjugateSubgroup actorElement.val target) ≤ _
    have equal : conjugateSubgroup conjugator (conjugateSubgroup actorElement.val target) =
        conjugateSubgroup (conjugator * actorElement.val * conjugator⁻¹)
          (conjugateSubgroup conjugator target) := by
      rw [conjugate_subgroup_mul, conjugate_subgroup_mul]
      congr 1
      group
    rw [equal]
    apply (Subgroup.map_mono (f := (MulAut.conj (conjugator * actorElement.val * conjugator⁻¹)).toMonoidHom)
      (normalized_conjugate_subgroup_le external target target_normalized conjugator conjugator_member)).trans
    exact le_iSup_of_le (⟨conjugator * actorElement.val * conjugator⁻¹,
      Subgroup.le_normalizer_iff.mp actor_normalized conjugator conjugator_member actorElement.val actorElement.property⟩ : actor)
      le_rfl
  exact image_le (Subgroup.mem_map_of_mem _ member)

variable [Finite GroupType]

theorem hall_prime_complement_sylow_product (sylowPrime : ℕ) (sylowPrime_prime : sylowPrime.Prime)
    (parent hall : Subgroup GroupType) (hall_le : hall ≤ parent)
    (hall_property : IsHallSubgroup ({sylowPrime}ᶜ) (hall.subgroupOf parent))
    (sylow : Sylow sylowPrime parent) :
    subgroupProduct hall ((sylow : Subgroup parent).map parent.subtype) = (parent : Set GroupType) := by
  let : Fact sylowPrime.Prime := ⟨sylowPrime_prime⟩
  let internalHall := hall.subgroupOf parent
  have hall_coprime : Nat.Coprime sylowPrime (Nat.card internalHall) :=
    (prime_supported_complement_singleton_iff_coprime sylowPrime sylowPrime_prime _).mp hall_property.1
  have index_supported : primeSupported {sylowPrime} internalHall.index := by
    simpa only [compl_compl] using hall_property.2
  have index_power : internalHall.index = sylowPrime ^ internalHall.index.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd Subgroup.index_ne_zero_of_finite
      (fun divisor_prime divides => index_supported _ divisor_prime divides)
  have index_equal : internalHall.index = Nat.card (sylow : Subgroup parent) := by
    have orders := congrArg (fun cardinality : ℕ => cardinality.factorization sylowPrime)
      (Subgroup.card_mul_index internalHall)
    rw [Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd
        (sylowPrime_prime.coprime_iff_not_dvd.mp hall_coprime), zero_add] at orders
    rw [sylow.card_eq_multiplicity, ← orders, index_power,
      Nat.factorization_pow_self sylowPrime_prime]
  have intersection_bot : internalHall ⊓ (sylow : Subgroup parent) = ⊥ := by
    have intersection_prime := sylow.isPGroup'.to_le
      (show internalHall ⊓ (sylow : Subgroup parent) ≤ sylow from inf_le_right)
    have intersection_coprime := hall_coprime.of_dvd_right
      (Subgroup.card_dvd_of_le (show internalHall ⊓ (sylow : Subgroup parent) ≤ internalHall from inf_le_left))
    rcases intersection_prime.card_eq_or_dvd with equal | divides
    · exact (Subgroup.eq_bot_iff_card _).mpr equal
    · exact (sylowPrime_prime.coprime_iff_not_dvd.mp intersection_coprime divides).elim
  have internal_product : subgroupProduct internalHall (sylow : Subgroup parent) = Set.univ := by
    have cardinality := Subgroup.card_mul_index internalHall
    rw [index_equal] at cardinality
    have product := subgroup_product_eq_of_card_formula (⊤ : Subgroup parent) internalHall
      (sylow : Subgroup parent) le_top le_top (by
        simpa only [Subgroup.card_top, intersection_bot, Subgroup.card_bot, mul_one] using cardinality)
    simpa only [Subgroup.coe_top] using product
  apply (subgroup_product_eq_subgroup_iff parent hall _ hall_le (Subgroup.map_subtype_le _)).mpr
  intro element member
  obtain ⟨hallElement, hall_member, sylowElement, sylow_member, product⟩ :=
    (subgroup_product_eq_univ_iff internalHall (sylow : Subgroup parent)).mp internal_product ⟨element, member⟩
  exact ⟨hallElement.val, hall_member, sylowElement.val, Subgroup.mem_map_of_mem parent.subtype sylow_member,
    congrArg (fun internal : parent => internal.val) product⟩

theorem normalized_hall_intersection (prime : ℕ) (prime_prime : prime.Prime)
    (actor parent hall target : Subgroup GroupType) (actor_pgroup : IsPGroup prime actor)
    (parent_solvable : Group.IsSolvable parent) (coprime : Nat.Coprime prime (Nat.card parent))
    (parent_normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (hall_normalized : actor ≤ Subgroup.normalizer (hall : Set GroupType))
    (target_normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (target_le : target ≤ parent) (primes : Set ℕ)
    (hall_property : IsHallSubgroup primes (hall.subgroupOf parent))
    (fixed_normalized : parent ⊓ Subgroup.centralizer (actor : Set GroupType) ≤
      Subgroup.normalizer (target : Set GroupType)) : IsHallSubgroup primes (hall.subgroupOf target) := by
  let := parent_solvable
  let _action := conjugationAction actor parent parent_normalized
  have internal_fixed : FixedPoints.subgroup actor parent ≤
      Subgroup.normalizer (target.subgroupOf parent : Set parent) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro conjugator conjugator_fixed element member
    exact Subgroup.le_normalizer_iff.mp fixed_normalized conjugator.val
      ((conjugation_fixed_subgroup_map actor parent parent_normalized).le
        (Subgroup.mem_map_of_mem parent.subtype conjugator_fixed)) element.val member
  have intersection := (invariant_hall_normalized_intersection prime prime_prime actor actor_pgroup
    coprime primes (hall.subgroupOf parent) (target.subgroupOf parent) hall_property
    (normalized_subgroupOf_invariant actor parent hall parent_normalized hall_normalized)
    (normalized_subgroupOf_invariant actor parent target parent_normalized target_normalized) internal_fixed).1
  let equivalence := Subgroup.subgroupOfEquivOfLe target_le
  have mapped := hall_map_surjective primes equivalence.toMonoidHom equivalence.surjective _ intersection
  have equal : ((hall.subgroupOf parent).subgroupOf (target.subgroupOf parent)).map equivalence.toMonoidHom =
      hall.subgroupOf target := by
    ext element
    constructor
    · rintro ⟨representative, member, image⟩
      have values := congrArg (fun candidate : target => candidate.val) image
      change representative.val.val = element.val at values
      change element.val ∈ hall
      rwa [← values]
    · intro member
      exact ⟨⟨⟨element.val, target_le element.property⟩, element.property⟩, member, Subtype.ext rfl⟩
  rwa [equal] at mapped

theorem normalized_invariant_hall_containing (prime : ℕ) (prime_prime : prime.Prime)
    (actor parent target : Subgroup GroupType) (actor_pgroup : IsPGroup prime actor)
    (parent_solvable : Group.IsSolvable parent) (coprime : Nat.Coprime prime (Nat.card parent))
    (parent_normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (target_le : target ≤ parent) (target_normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (primes : Set ℕ) (supported : primeSupported primes (Nat.card target)) :
    ∃ hall : Subgroup GroupType, target ≤ hall ∧ hall ≤ parent ∧
      IsHallSubgroup primes (hall.subgroupOf parent) ∧ actor ≤ Subgroup.normalizer (hall : Set GroupType) := by
  let := parent_solvable
  let _action := conjugationAction actor parent parent_normalized
  have internal_supported : primeSupported primes (Nat.card (target.subgroupOf parent)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe target_le).toEquiv]
    exact supported
  obtain ⟨internalHall, contains, hall_property, invariant⟩ := invariant_hall_subgroup_containing prime prime_prime
    actor actor_pgroup parent coprime primes (target.subgroupOf parent) internal_supported
      (normalized_subgroupOf_invariant actor parent target parent_normalized target_normalized)
  refine ⟨internalHall.map parent.subtype, ?_, Subgroup.map_subtype_le _, ?_,
    invariant_subgroup_map_normalized actor parent parent_normalized internalHall invariant⟩
  · have mapped := Subgroup.map_mono (f := parent.subtype) contains
    rwa [Subgroup.map_subgroupOf_eq_of_le target_le] at mapped
  · change IsHallSubgroup primes ((internalHall.map parent.subtype).comap parent.subtype)
    rwa [Subgroup.comap_map_eq_self_of_injective parent.subtype_injective]

variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_hall_product_common_fixed_eq
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (common_le_parent : signalizerCommonFixed prime rank actor values ≤ parent) :
    signalizerCommonFixed prime rank actor values = parent ⊓ Subgroup.centralizer (actor : Set GroupType) := by
  apply le_antisymm (le_inf common_le_parent inf_le_left)
  apply le_inf inf_le_right
  apply le_iInf
  intro selected
  apply le_iInf
  intro member
  exact (inf_le_inf_left _ (Subgroup.centralizer_le member.1)).trans
    ((incomplete_hall_product_full_centralizers datum selected member).symm.le.trans inf_le_left)

end CFSG.SignalizerFunctor.Helpers
