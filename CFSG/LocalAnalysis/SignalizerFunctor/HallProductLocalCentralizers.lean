module

public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerFactorization
public import CFSG.LocalAnalysis.SignalizerFunctor.IncompleteHallProduct
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvablePrimeCore
public import CFSG.LocalAnalysis.SignalizerFunctor.SylowFixedIntersections

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_hall_product_local_fixed_solvable (fixedActor selected : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (selected_member : selected ∈ signalizerFunctorEk prime rank actor) (selected_le : selected ≤ fixedActor) :
    Group.IsSolvable (parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType) : Subgroup GroupType) := by
  let _solvable := datum.conditions.solvable selected selected_member
  have contained : parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType) ≤ values selected :=
    (inf_le_inf_left _ (Subgroup.centralizer_le selected_le)).trans
      ((incomplete_hall_product_full_centralizers datum selected selected_member).symm.le.trans inf_le_left)
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective contained)

omit [Finite GroupType] in
theorem incomplete_hall_product_local_fixed_normalized (fixedActor : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (fixedActor_le : fixedActor ≤ actor) :
    actor ≤ Subgroup.normalizer
      ((parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType) : Subgroup GroupType) : Set GroupType) := by
  have centralizer_normalized :=
    (elementary_abelian_le_centralizer prime actor fixedActor datum.elementary fixedActor_le).trans Subgroup.le_normalizer
  exact normalizer_inf_of_le actor _ _ datum.parent_normalized centralizer_normalized

theorem incomplete_hall_product_local_fixed_sylow (fixedActor : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (fixedActor_le : fixedActor ≤ actor) :
    ∃ sylow : Sylow groupPrime (parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType) : Subgroup GroupType),
      (sylow : Subgroup (parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType) : Subgroup GroupType)).map
        (parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)).subtype =
          factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType) := by
  obtain ⟨parentSylow, parentSylow_eq⟩ := incomplete_hall_product_factor_parent_sylow datum
  have embedded_eq : (parentSylow : Subgroup parent).map parent.subtype = factor := by
    rw [parentSylow_eq, Subgroup.map_subgroupOf_eq_of_le datum.factor_le]
  have parent_normalized : fixedActor ≤ Subgroup.normalizer (parent : Set GroupType) :=
    fixedActor_le.trans datum.parent_normalized
  have sylow_normalized : fixedActor ≤ Subgroup.normalizer
      (((parentSylow : Subgroup parent).map parent.subtype : Subgroup GroupType) : Set GroupType) := by
    rw [embedded_eq]
    exact fixedActor_le.trans datum.factor_compatible.1
  obtain ⟨sylow, equal⟩ := normalized_sylow_centralizer_intersection prime groupPrime datum.prime_prime
    datum.groupPrime_prime fixedActor parent ((elementary_abelian_isPGroup prime actor datum.elementary).to_le fixedActor_le)
    parent_normalized (incomplete_hall_product_parent_coprime datum) parentSylow sylow_normalized
  exact ⟨sylow, by rwa [embedded_eq] at equal⟩

theorem solvable_trivial_sylow_complement_core_eq_top [Group.IsSolvable GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (sylow : Sylow prime GroupType)
    (trivial : (sylow : Subgroup GroupType) = ⊥) : primeSetCore (GroupType := GroupType) ({prime}ᶜ) = ⊤ := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  have coprime : Nat.Coprime prime (Nat.card GroupType) := by
    apply prime_prime.coprime_iff_not_dvd.mpr
    have not_divides := sylow.not_dvd_index
    rw [trivial, Subgroup.index_bot] at not_divides
    exact not_divides
  apply top_unique
  apply prime_set_core_contains
  · infer_instance
  · rw [Subgroup.card_top]
    exact (prime_supported_complement_singleton_iff_coprime prime prime_prime _).mpr coprime

theorem incomplete_abelian_hall_product_local_normalizer_product (fixedActor selected : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (fixedActor_le : fixedActor ≤ actor)
    (selected_member : selected ∈ signalizerFunctorEk prime rank actor) (selected_le : selected ≤ fixedActor) :
    let localFixed := parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
    let localCore := (primeSetCore (GroupType := localFixed) ({groupPrime}ᶜ)).map localFixed.subtype
    subgroupProduct localCore (localFixed ⊓ Subgroup.normalizer (factor : Set GroupType)) = (localFixed : Set GroupType) := by
  let localFixed := parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  let localFactor := factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  let internalCore := primeSetCore (GroupType := localFixed) ({groupPrime}ᶜ)
  let localCore := internalCore.map localFixed.subtype
  let localNormalizer := localFixed ⊓ Subgroup.normalizer (factor : Set GroupType)
  change subgroupProduct localCore localNormalizer = (localFixed : Set GroupType)
  let _solvable := incomplete_hall_product_local_fixed_solvable fixedActor selected datum selected_member selected_le
  have fixed_normalized := incomplete_hall_product_local_fixed_normalized fixedActor datum fixedActor_le
  have factor_normalized : actor ≤ Subgroup.normalizer (localFactor : Set GroupType) :=
    normalizer_inf_of_le actor _ _ datum.factor_compatible.1
      ((elementary_abelian_le_centralizer prime actor fixedActor datum.elementary fixedActor_le).trans Subgroup.le_normalizer)
  obtain ⟨sylow, sylow_eq⟩ := incomplete_hall_product_local_fixed_sylow fixedActor datum fixedActor_le
  let := abelian
  have sylow_abelian : IsMulCommutative (sylow : Subgroup localFixed) := by
    apply Subgroup.le_centralizer_iff_isMulCommutative.mp
    intro element member
    apply Subgroup.mem_centralizer_iff.mpr
    intro other other_member
    apply Subtype.ext
    have element_factor : element.val ∈ factor := by
      have mapped_member := Subgroup.mem_map_of_mem localFixed.subtype member
      rw [sylow_eq] at mapped_member
      exact mapped_member.1
    have other_factor : other.val ∈ factor := by
      have mapped_member := Subgroup.mem_map_of_mem localFixed.subtype other_member
      rw [sylow_eq] at mapped_member
      exact mapped_member.1
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.le_centralizer factor element_factor) other.val other_factor
  have join_eq : localCore ⊔ localNormalizer = localFixed := by
    apply le_antisymm (sup_le (Subgroup.map_subtype_le _) inf_le_left)
    by_cases trivial : localFactor = ⊥
    · have internal_trivial : (sylow : Subgroup localFixed) = ⊥ := by
        apply (Subgroup.map_eq_bot_iff_of_injective _ localFixed.subtype_injective).mp
        exact sylow_eq.trans trivial
      have core_top := solvable_trivial_sylow_complement_core_eq_top groupPrime datum.groupPrime_prime sylow internal_trivial
      have core_eq : localCore = localFixed := by
        change (primeSetCore (GroupType := localFixed) ({groupPrime}ᶜ)).map localFixed.subtype = localFixed
        rw [core_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact core_eq.symm.le.trans le_sup_left
    · have trap := incomplete_abelian_hall_product_subgroup_normalizer_trap localFactor datum abelian
        inf_le_left trivial factor_normalized
      have factorization := solvable_abelian_sylow_normalizer_factorization groupPrime datum.groupPrime_prime sylow sylow_abelian
      have mapped_eq := congrArg (Subgroup.map localFixed.subtype) factorization
      rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at mapped_eq
      have normalizer_formula := normalizer_subtype_map localFixed (sylow : Subgroup localFixed)
      rw [sylow_eq] at normalizer_formula
      have local_normalizer_le : (Subgroup.normalizer (sylow : Set localFixed)).map localFixed.subtype ≤ localNormalizer := by
        change (Subgroup.normalizer ((sylow : Subgroup localFixed) : Set localFixed)).map localFixed.subtype ≤ _
        rw [normalizer_formula]
        exact le_inf inf_le_left ((le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans trap.2)
      apply mapped_eq.symm.le.trans
      exact sup_le le_sup_left (local_normalizer_le.trans le_sup_right)
  let _coreCharacteristic := prime_set_core_characteristic (GroupType := localFixed) ({groupPrime}ᶜ)
  have core_normalized : localNormalizer ≤ Subgroup.normalizer (localCore : Set GroupType) :=
    inf_le_left.trans (characteristic_subgroup_map_normalized localFixed localFixed Subgroup.le_normalizer internalCore)
  apply (subgroup_product_eq_subgroup_iff localFixed localCore localNormalizer (Subgroup.map_subtype_le _) inf_le_left).mpr
  intro element member
  exact (mem_sup_of_normalizing localCore localNormalizer core_normalized element).mp (by rwa [join_eq])

theorem incomplete_hall_product_factor_prime_in_spectrum
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values) :
    groupPrime ∈ signalizerSpectrum prime rank actor values := by
  let : Fact groupPrime.Prime := ⟨datum.groupPrime_prime⟩
  have divides : groupPrime ∣ Nat.card factor := by
    rcases datum.factor_pgroup.card_eq_or_dvd with equal | divides
    · exact ((incomplete_hall_product_factor_nontrivial datum) ((Subgroup.eq_bot_iff_card _).mpr equal)).elim
    · exact divides
  obtain ⟨selected, member, value_divides⟩ := signalizer_compatible_prime_support prime rank groupPrime
    datum.prime_prime datum.groupPrime_prime actor datum.elementary datum.large values datum.conditions.coprime
    factor datum.factor_compatible divides
  exact ⟨datum.groupPrime_prime, selected, member, value_divides⟩

theorem incomplete_hall_product_local_core_le_prime_completion (fixedActor selected : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (fixedActor_le : fixedActor ≤ actor) (selected_member : selected ∈ signalizerFunctorEk prime rank actor)
    (selected_le : selected ≤ fixedActor)
    (common_le_parent : signalizerCommonFixed prime rank actor values ≤ parent) :
    let localFixed := parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
    (primeSetCore (GroupType := localFixed) ({groupPrime}ᶜ)).map localFixed.subtype ≤
      signalizerPrimeCompletion prime rank actor values (signalizerSpectrum prime rank actor values \ {groupPrime}) := by
  let localFixed := parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  let internalCore := primeSetCore (GroupType := localFixed) ({groupPrime}ᶜ)
  let localCore := internalCore.map localFixed.subtype
  let _characteristic := prime_set_core_characteristic (GroupType := localFixed) ({groupPrime}ᶜ)
  have fixed_normalized := incomplete_hall_product_local_fixed_normalized fixedActor datum fixedActor_le
  have core_normalized := characteristic_subgroup_map_normalized actor localFixed fixed_normalized internalCore
  have common_le : signalizerCommonFixed prime rank actor values ≤ localFixed :=
    le_inf common_le_parent (inf_le_left.trans (Subgroup.centralizer_le fixedActor_le))
  have common_normalized := characteristic_subgroup_map_normalized _ localFixed
    (common_le.trans Subgroup.le_normalizer) internalCore
  have compatible := incomplete_hall_product_normalized_compatible localCore datum
    ((Subgroup.map_subtype_le internalCore).trans inf_le_left) core_normalized
  have fixed_le_value : localFixed ≤ values selected :=
    (inf_le_inf_left _ (Subgroup.centralizer_le selected_le)).trans
      ((incomplete_hall_product_full_centralizers datum selected selected_member).symm.le.trans inf_le_left)
  have core_coprime : Nat.Coprime groupPrime (Nat.card localCore) := by
    rw [Subgroup.card_map_of_injective localFixed.subtype_injective]
    exact (prime_supported_complement_singleton_iff_coprime groupPrime datum.groupPrime_prime _).mp
      (prime_set_core_supported ({groupPrime}ᶜ))
  have supported : primeSupported (signalizerSpectrum prime rank actor values \ {groupPrime}) (Nat.card localCore) := by
    intro divisor divisor_prime divides
    refine ⟨⟨divisor_prime, selected, selected_member,
      divides.trans (Subgroup.card_dvd_of_le ((Subgroup.map_subtype_le internalCore).trans fixed_le_value))⟩, ?_⟩
    intro equal
    exact datum.groupPrime_prime.coprime_iff_not_dvd.mp core_coprime (equal ▸ divides)
  have complete := (datum.locally_complete.2 groupPrime (incomplete_hall_product_factor_prime_in_spectrum datum)).1
  exact (signalizer_prime_completion_control prime rank datum.prime_prime actor datum.elementary datum.large values
    datum.conditions _ complete).2.2.2 localCore compatible supported common_normalized

end CFSG.SignalizerFunctor.Helpers
