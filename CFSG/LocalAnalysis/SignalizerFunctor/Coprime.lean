module

public import CFSG.LocalAnalysis.SignalizerFunctor.Helpers

public section

open CFSG.Open

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

abbrev conjugationAction (actor target : Subgroup GroupType)
    (normalizes : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    MulDistribMulAction actor target where
  smul actorElement targetElement :=
    ⟨actorElement * targetElement * (actorElement : GroupType)⁻¹,
      Subgroup.le_normalizer_iff.mp normalizes actorElement actorElement.property
        targetElement targetElement.property⟩
  one_smul targetElement := by
    apply Subtype.ext
    change (1 : GroupType) * targetElement * (1 : GroupType)⁻¹ = targetElement
    simp
  mul_smul first second targetElement := by
    apply Subtype.ext
    change ((first : GroupType) * second) * targetElement *
        ((first : GroupType) * second)⁻¹ =
      first * (second * targetElement * (second : GroupType)⁻¹) *
        (first : GroupType)⁻¹
    simp [mul_assoc]
  smul_one actorElement := by
    apply Subtype.ext
    change (actorElement : GroupType) * 1 * (actorElement : GroupType)⁻¹ = 1
    simp
  smul_mul actorElement first second := by
    apply Subtype.ext
    change (actorElement : GroupType) * (first * second) *
        (actorElement : GroupType)⁻¹ =
      (actorElement * first * (actorElement : GroupType)⁻¹) *
        (actorElement * second * (actorElement : GroupType)⁻¹)
    simp [mul_assoc]

variable {ActorType : Type actorUniverse} [Group ActorType]

theorem conjugation_fixed_subgroup_map (actor target : Subgroup GroupType)
    (normalizes : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    let _action := conjugationAction actor target normalizes
    (FixedPoints.subgroup actor target).map target.subtype =
      target ⊓ Subgroup.centralizer (actor : Set GroupType) := by
  let _action := conjugationAction actor target normalizes
  ext element
  constructor
  · rintro ⟨internal, fixed, rfl⟩
    refine ⟨internal.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro actorElement member
    have equality := congrArg (fun value : target => (value : GroupType))
      (fixed (⟨actorElement, member⟩ : actor))
    change actorElement * internal * actorElement⁻¹ = internal at equality
    exact mul_inv_eq_iff_eq_mul.mp equality
  · rintro ⟨member, central⟩
    refine ⟨⟨element, member⟩, ?_, rfl⟩
    intro actorElement
    apply Subtype.ext
    change (actorElement : GroupType) * element * (actorElement : GroupType)⁻¹ = element
    exact mul_inv_eq_iff_eq_mul.mpr
      (Subgroup.mem_centralizer_iff.mp central actorElement actorElement.property)

theorem centralizer_card_modEq [Finite GroupType] (prime : ℕ)
    (prime_prime : prime.Prime) (actor target : Subgroup GroupType)
    (actor_pgroup : IsPGroup prime actor)
    (normalizes : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    Nat.card target ≡
      Nat.card ↥(target ⊓ Subgroup.centralizer (actor : Set GroupType)) [MOD prime] := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let _action := conjugationAction actor target normalizes
  have fixed_card :
      Nat.card (MulAction.fixedPoints actor target) =
        Nat.card ↥(target ⊓ Subgroup.centralizer (actor : Set GroupType)) := by
    change Nat.card (FixedPoints.subgroup actor target) = _
    rw [← conjugation_fixed_subgroup_map actor target normalizes]
    exact (Subgroup.card_map_of_injective target.subtype_injective).symm
  exact fixed_card ▸ actor_pgroup.card_modEq_card_fixedPoints target

theorem coprime_of_centralizer_coprime [Finite GroupType] (prime : ℕ)
    (prime_prime : prime.Prime) (actor target : Subgroup GroupType)
    (actor_pgroup : IsPGroup prime actor)
    (normalizes : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (centralizer_coprime :
      Nat.Coprime prime (Nat.card ↥(target ⊓ Subgroup.centralizer (actor : Set GroupType)))) :
    Nat.Coprime prime (Nat.card target) := by
  rw [prime_prime.coprime_iff_not_dvd] at centralizer_coprime ⊢
  exact fun divides => centralizer_coprime
    ((centralizer_card_modEq prime prime_prime actor target actor_pgroup normalizes).dvd_iff
      dvd_rfl |>.mp divides)

theorem signalizer_subgroup_coprime [Finite GroupType] (prime rank : ℕ)
    (prime_prime : prime.Prime) (actor : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor)
    (large : prime ^ rank ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (values_coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (target : Subgroup GroupType)
    (normalizes : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (fixed_contained : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      target ⊓ Subgroup.centralizer (subgroup : Set GroupType) ≤ values subgroup) :
    Nat.Coprime prime (Nat.card target) := by
  obtain ⟨subgroup, member⟩ :=
    signalizerFunctorEk_nonempty prime rank prime_prime actor elementary large
  exact coprime_of_centralizer_coprime prime prime_prime subgroup target
    (elementary_abelian_isPGroup prime subgroup
      (elementary_abelian_of_le prime elementary member.1))
    (member.1.trans normalizes)
    ((values_coprime subgroup member).of_dvd_right
      (Subgroup.card_dvd_of_le (fixed_contained subgroup member)))

theorem invariant_sylow_exists [Finite GroupType] (prime sylowPrime : ℕ)
    (prime_prime : prime.Prime) (sylowPrime_prime : sylowPrime.Prime)
    (actor_pgroup : IsPGroup prime ActorType)
    [MulDistribMulAction ActorType GroupType]
    (coprime : Nat.Coprime prime (Nat.card GroupType)) :
    ∃ sylow : Sylow sylowPrime GroupType,
      ∀ actorElement : ActorType, actorElement • sylow = sylow := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let : Fact sylowPrime.Prime := ⟨sylowPrime_prime⟩
  have sylow_card_dvd : Nat.card (Sylow sylowPrime GroupType) ∣ Nat.card GroupType :=
    (Sylow.card_dvd_index (Classical.choice inferInstance)).trans
      (Subgroup.index_dvd_card _)
  obtain ⟨sylow, fixed⟩ := actor_pgroup.nonempty_fixed_point_of_prime_not_dvd_card
    (Sylow sylowPrime GroupType)
    (prime_prime.coprime_iff_not_dvd.mp (coprime.of_dvd_right sylow_card_dvd))
  exact ⟨sylow, fixed⟩

end CFSG.SignalizerFunctor.Helpers
