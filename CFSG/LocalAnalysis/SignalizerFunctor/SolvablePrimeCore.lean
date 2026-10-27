module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedGrowth
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvableFitting

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem distinct_prime_core_le_complement_core (prime other : ℕ)
    (prime_prime : prime.Prime) (other_prime : other.Prime) (distinct : prime ≠ other) :
    primeSetCore (GroupType := GroupType) {other} ≤ primeSetCore ({prime}ᶜ) := by
  apply prime_set_core_contains
  · exact prime_set_core_normal {other}
  · apply (prime_supported_complement_singleton_iff_coprime prime prime_prime _).mpr
    exact prime_coprime_pgroup_card prime other prime_prime other_prime distinct
      (prime_core_isPGroup other other_prime)

theorem fitting_eq_prime_core_of_complement_core_trivial (prime : ℕ) (prime_prime : prime.Prime)
    (trivial : primeSetCore (GroupType := GroupType) ({prime}ᶜ) = ⊥) :
    fittingSubgroup (GroupType := GroupType) = primeSetCore {prime} := by
  rw [fitting_subgroup_eq_prime_cores]
  apply le_antisymm
  · apply iSup_le
    intro other
    by_cases same : other.val = prime
    · rw [same]
    · have contained := distinct_prime_core_le_complement_core (GroupType := GroupType) prime other.val
        prime_prime other.property (Ne.symm same)
      rw [trivial] at contained
      exact contained.trans bot_le
  · exact le_iSup (fun other : {other : ℕ // other.Prime} => primeSetCore {other.val}) ⟨prime, prime_prime⟩

theorem solvable_prime_core_self_centralizing [Group.IsSolvable GroupType]
    (prime : ℕ) (prime_prime : prime.Prime)
    (trivial : primeSetCore (GroupType := GroupType) ({prime}ᶜ) = ⊥) :
    Subgroup.centralizer (primeSetCore (GroupType := GroupType) {prime} : Set GroupType) ≤ primeSetCore {prime} := by
  rw [← fitting_eq_prime_core_of_complement_core_trivial prime prime_prime trivial]
  exact solvable_fitting_centralizer_le

theorem solvable_complement_core_quotient_characteristic_prime [Group.IsSolvable GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) :
    let complement := primeSetCore (GroupType := GroupType) ({prime}ᶜ)
    let _normal := prime_set_core_normal (GroupType := GroupType) ({prime}ᶜ)
    Subgroup.centralizer (primeSetCore (GroupType := GroupType ⧸ complement) {prime} : Set (GroupType ⧸ complement)) ≤
      primeSetCore {prime} := by
  let complement := primeSetCore (GroupType := GroupType) ({prime}ᶜ)
  let _normal := prime_set_core_normal (GroupType := GroupType) ({prime}ᶜ)
  exact solvable_prime_core_self_centralizing prime prime_prime (prime_set_core_quotient_trivial ({prime}ᶜ))

theorem solvable_abelian_sylow_quotient_eq_prime_core [Group.IsSolvable GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (sylow : Sylow prime GroupType)
    (abelian : IsMulCommutative (sylow : Subgroup GroupType)) :
    let complement := primeSetCore (GroupType := GroupType) ({prime}ᶜ)
    let _normal := prime_set_core_normal (GroupType := GroupType) ({prime}ᶜ)
    (sylow : Subgroup GroupType).map (QuotientGroup.mk' complement) =
      primeSetCore (GroupType := GroupType ⧸ complement) {prime} := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let := abelian
  let complement := primeSetCore (GroupType := GroupType) ({prime}ᶜ)
  let _normal := prime_set_core_normal (GroupType := GroupType) ({prime}ᶜ)
  let projection := QuotientGroup.mk' complement
  let quotientSylow := sylow.mapSurjective (QuotientGroup.mk'_surjective complement)
  let core := primeSetCore (GroupType := GroupType ⧸ complement) {prime}
  let _coreNormal := prime_set_core_normal (GroupType := GroupType ⧸ complement) {prime}
  have core_le : core ≤ (quotientSylow : Subgroup (GroupType ⧸ complement)) :=
    (prime_core_isPGroup prime prime_prime).le_sylow_of_normal quotientSylow
  have image_centralizes : (sylow : Subgroup GroupType).map projection ≤
      Subgroup.centralizer ((sylow : Subgroup GroupType).map projection : Set (GroupType ⧸ complement)) := by
    rintro _ ⟨first, first_member, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨second, second_member, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg projection (Subgroup.mem_centralizer_iff.mp
      (Subgroup.le_centralizer (sylow : Subgroup GroupType) first_member) second second_member)
  have image_le : (sylow : Subgroup GroupType).map projection ≤ core := by
    apply le_trans _ (solvable_complement_core_quotient_characteristic_prime prime prime_prime)
    apply image_centralizes.trans
    apply Subgroup.centralizer_le
    rw [Sylow.coe_mapSurjective] at core_le
    exact core_le
  apply le_antisymm image_le
  rwa [Sylow.coe_mapSurjective] at core_le

theorem solvable_abelian_sylow_normalizer_factorization [Group.IsSolvable GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (sylow : Sylow prime GroupType)
    (abelian : IsMulCommutative (sylow : Subgroup GroupType)) :
    primeSetCore (GroupType := GroupType) ({prime}ᶜ) ⊔ Subgroup.normalizer (sylow : Set GroupType) = ⊤ := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let complement := primeSetCore (GroupType := GroupType) ({prime}ᶜ)
  let _complementNormal := prime_set_core_normal (GroupType := GroupType) ({prime}ᶜ)
  have image_eq := solvable_abelian_sylow_quotient_eq_prime_core prime prime_prime sylow abelian
  have preimage_eq := congrArg (Subgroup.comap (QuotientGroup.mk' complement)) image_eq
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at preimage_eq
  have core_eq : complement ⊔ (sylow : Subgroup GroupType) = twoStageCore prime :=
    (sup_comm _ _).trans preimage_eq
  let _coreNormal := two_stage_core_normal (GroupType := GroupType) prime
  have factorization := sylow.normalizer_sup_eq_top' (N := twoStageCore prime)
    (by rw [← core_eq]; exact le_sup_right)
  apply top_le_iff.mp
  rw [← factorization, ← core_eq]
  exact sup_le le_sup_right (sup_le le_sup_left (Subgroup.le_normalizer.trans le_sup_right))

omit [Finite GroupType] in
theorem commutator_le_of_normalizing (target actor : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType)) : ⁅target, actor⁆ ≤ target := by
  apply Subgroup.commutator_le.mpr
  intro element member actorElement actor_member
  change element * actorElement * element⁻¹ * actorElement⁻¹ ∈ target
  have conjugated := Subgroup.le_normalizer_iff.mp normalized actorElement actor_member element⁻¹
    (target.inv_mem member)
  have product := target.mul_mem member conjugated
  simpa only [mul_assoc] using product

theorem solvable_sylow_normalized_complement_le_core [Group.IsSolvable GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (sylow : Sylow prime GroupType)
    (target : Subgroup GroupType) (coprime : Nat.Coprime prime (Nat.card target))
    (normalized : (sylow : Subgroup GroupType) ≤ Subgroup.normalizer (target : Set GroupType)) :
    target ≤ primeSetCore ({prime}ᶜ) := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let complement := primeSetCore (GroupType := GroupType) ({prime}ᶜ)
  let _complementNormal := prime_set_core_normal (GroupType := GroupType) ({prime}ᶜ)
  let projection := QuotientGroup.mk' complement
  let quotientSylow := sylow.mapSurjective (QuotientGroup.mk'_surjective complement)
  let core := primeSetCore (GroupType := GroupType ⧸ complement) {prime}
  let _coreNormal := prime_set_core_normal (GroupType := GroupType ⧸ complement) {prime}
  let image := target.map projection
  have image_coprime : Nat.Coprime prime (Nat.card image) := coprime.of_dvd_right (Subgroup.card_map_dvd target projection)
  have core_le := (prime_core_isPGroup (GroupType := GroupType ⧸ complement) prime prime_prime).le_sylow_of_normal quotientSylow
  have core_normalizes : core ≤ Subgroup.normalizer (image : Set (GroupType ⧸ complement)) := by
    apply core_le.trans
    rw [Sylow.coe_mapSurjective]
    exact (Subgroup.map_mono normalized).trans (Subgroup.le_normalizer_map projection)
  have intersection_bot : image ⊓ core = ⊥ := by
    obtain ⟨exponent, cardinality⟩ :=
      (prime_core_isPGroup (GroupType := GroupType ⧸ complement) prime prime_prime).exists_card_eq
    have orders_coprime : Nat.Coprime (Nat.card image) (Nat.card core) := by
      rw [cardinality]
      exact prime_prime.coprime_pow_of_not_dvd (prime_prime.coprime_iff_not_dvd.mp image_coprime)
    have disjoint := Subgroup.disjoint_of_coprime_natCard orders_coprime
    exact disjoint.eq_bot
  have commutator_bot : ⁅image, core⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← intersection_bot]
    exact le_inf (commutator_le_of_normalizing image core core_normalizes) (Subgroup.commutator_le_right _ _)
  have image_le : image ≤ core :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp commutator_bot).trans
      (solvable_complement_core_quotient_characteristic_prime prime prime_prime)
  have image_bot : image = ⊥ := le_bot_iff.mp ((le_inf le_rfl image_le).trans intersection_bot.le)
  intro element member
  apply (QuotientGroup.eq_one_iff _).mp
  have mapped_member := Subgroup.mem_map_of_mem projection member
  change projection element ∈ image at mapped_member
  rw [image_bot] at mapped_member
  exact mapped_member

end CFSG.SignalizerFunctor.Helpers
