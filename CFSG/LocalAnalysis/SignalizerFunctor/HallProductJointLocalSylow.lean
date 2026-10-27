module

public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductLocalCentralizers
public import CFSG.LocalAnalysis.SignalizerFunctor.JointInvariantSylow

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_hall_product_joint_local_core_sylow (fixedActor selected : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (fixedActor_le : fixedActor ≤ actor) (selected_member : selected ∈ signalizerFunctorEk prime rank actor)
    (selected_le : selected ≤ fixedActor) (sylowPrime : ℕ) (sylowPrime_prime : sylowPrime.Prime) :
    let localFixed := parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
    let localCore := (primeSetCore (GroupType := localFixed) ({groupPrime}ᶜ)).map localFixed.subtype
    let localFactor := factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
    ∃ sylow : Sylow sylowPrime localCore,
      actor ≤ Subgroup.normalizer
        (((sylow : Subgroup localCore).map localCore.subtype : Subgroup GroupType) : Set GroupType) ∧
      localFactor ≤ Subgroup.normalizer
        (((sylow : Subgroup localCore).map localCore.subtype : Subgroup GroupType) : Set GroupType) := by
  let localFixed := parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  let internalCore := primeSetCore (GroupType := localFixed) ({groupPrime}ᶜ)
  let localCore := internalCore.map localFixed.subtype
  let localFactor := factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  change ∃ sylow : Sylow sylowPrime localCore, actor ≤ Subgroup.normalizer
    (((sylow : Subgroup localCore).map localCore.subtype : Subgroup GroupType) : Set GroupType) ∧
    localFactor ≤ Subgroup.normalizer
      (((sylow : Subgroup localCore).map localCore.subtype : Subgroup GroupType) : Set GroupType)
  let _solvable := incomplete_hall_product_local_fixed_solvable fixedActor selected datum selected_member selected_le
  let _characteristic := prime_set_core_characteristic (GroupType := localFixed) ({groupPrime}ᶜ)
  have fixed_normalized := incomplete_hall_product_local_fixed_normalized fixedActor datum fixedActor_le
  have core_normalized := characteristic_subgroup_map_normalized actor localFixed fixed_normalized internalCore
  have factor_normalized : actor ≤ Subgroup.normalizer (localFactor : Set GroupType) :=
    normalizer_inf_of_le actor _ _ datum.factor_compatible.1
      ((elementary_abelian_le_centralizer prime actor fixedActor datum.elementary fixedActor_le).trans Subgroup.le_normalizer)
  have factor_fixed : localFactor ≤ localFixed := inf_le_inf_right _ datum.factor_le
  have factor_normalizes_core := factor_fixed.trans
    (characteristic_subgroup_map_normalized localFixed localFixed Subgroup.le_normalizer internalCore)
  have core_solvable : Group.IsSolvable localCore := by
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (Subgroup.map_subtype_le internalCore))
      (Subgroup.inclusion_injective (Subgroup.map_subtype_le internalCore))
  have core_coprime : Nat.Coprime prime (Nat.card localCore) :=
    (incomplete_hall_product_parent_coprime datum).of_dvd_right
      (Subgroup.card_dvd_of_le ((Subgroup.map_subtype_le internalCore).trans inf_le_left))
  have core_second_coprime : Nat.Coprime groupPrime (Nat.card localCore) := by
    rw [Subgroup.card_map_of_injective localFixed.subtype_injective]
    exact (prime_supported_complement_singleton_iff_coprime groupPrime datum.groupPrime_prime _).mp
      (prime_set_core_supported ({groupPrime}ᶜ))
  have bottom_pgroup : IsPGroup sylowPrime (⊥ : Subgroup GroupType) := by
    intro element
    exact ⟨0, by
      have identity : element = 1 := Subtype.ext element.property
      rw [identity]
      simp⟩
  obtain ⟨sylow, _, normalized, second_normalized⟩ := jointly_normalized_sylow_containing prime groupPrime sylowPrime
    datum.prime_prime datum.groupPrime_prime sylowPrime_prime actor localFactor localCore ⊥
    (elementary_abelian_isPGroup prime actor datum.elementary) (datum.factor_pgroup.to_le inf_le_left)
    factor_normalized core_solvable core_coprime core_second_coprime core_normalized factor_normalizes_core
    bot_le bottom_pgroup Subgroup.le_normalizer_of_normal Subgroup.le_normalizer_of_normal
  exact ⟨sylow, normalized, second_normalized⟩

end CFSG.SignalizerFunctor.Helpers
