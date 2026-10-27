module

public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductFixedCoreEscape
public import CFSG.LocalAnalysis.SignalizerFunctor.SubgroupProductIndices
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalizedProductFixedPoints

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_abelian_hall_product_local_commutator_nontrivial
    (fixedActor selected kernel : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (fixedActor_le : fixedActor ≤ actor)
    (selected_member : selected ∈ signalizerFunctorEk prime rank actor) (selected_le : selected ≤ fixedActor)
    (common_le_parent : signalizerCommonFixed prime rank actor values ≤ parent)
    (localFactor_nontrivial : factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType) ≠ ⊥)
    (kernel_le : kernel ≤ complement) (kernel_nontrivial : kernel ≠ ⊥)
    (kernel_normal : (kernel.subgroupOf complement).Normal)
    (kernel_normalized : actor ≤ Subgroup.normalizer (kernel : Set GroupType))
    (common_normalized : signalizerCommonFixed prime rank actor values ≤ Subgroup.normalizer (kernel : Set GroupType))
    (kernelPrime : ℕ) (kernelPrime_prime : kernelPrime.Prime)
    (kernelPrime_spectrum : kernelPrime ∈ signalizerSpectrum prime rank actor values)
    (kernelPrime_distinct : kernelPrime ≠ groupPrime) (kernel_coprime : Nat.Coprime kernelPrime (Nat.card kernel)) :
    let localFixed := parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
    let localCore := (primeSetCore (GroupType := localFixed) ({groupPrime}ᶜ)).map localFixed.subtype
    ∀ sylow : Sylow kernelPrime localCore,
      actor ≤ Subgroup.normalizer (((sylow : Subgroup localCore).map localCore.subtype : Subgroup GroupType) : Set GroupType) →
      (⁅(sylow : Subgroup localCore).map localCore.subtype,
        factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)⁆ : Subgroup GroupType) ≠ ⊥ := by
  classical
  let localFixed := parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  let internalCore := primeSetCore (GroupType := localFixed) ({groupPrime}ᶜ)
  let localCore := internalCore.map localFixed.subtype
  let localFactor := factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  let localNormalizer := localFixed ⊓ Subgroup.normalizer (factor : Set GroupType)
  let common := parent ⊓ Subgroup.centralizer (actor : Set GroupType)
  let commonCore := (primeSetCore (GroupType := common) ({groupPrime}ᶜ)).map common.subtype
  let control := common ⊓ Subgroup.normalizer (factor : Set GroupType)
  change ∀ sylow : Sylow kernelPrime localCore, _ → _
  intro sylow sylow_normalized commutator_trivial
  let witness := (sylow : Subgroup localCore).map localCore.subtype
  have parent_coprime := incomplete_hall_product_parent_coprime datum
  have actor_pgroup := elementary_abelian_isPGroup prime actor datum.elementary
  have localFixed_normalized := incomplete_hall_product_local_fixed_normalized fixedActor datum fixedActor_le
  have localFactor_normalized := normalizer_inf_of_le actor factor
    (Subgroup.centralizer (fixedActor : Set GroupType)) datum.factor_compatible.1
      ((elementary_abelian_le_centralizer prime actor fixedActor datum.elementary fixedActor_le).trans Subgroup.le_normalizer)
  let _coreCharacteristic := prime_set_core_characteristic (GroupType := localFixed) ({groupPrime}ᶜ)
  have localCore_normalized := characteristic_subgroup_map_normalized actor localFixed localFixed_normalized internalCore
  have localCore_le : localCore ≤ localFixed := Subgroup.map_subtype_le _
  have localNormalizer_normalized := normalizer_inf_of_le actor localFixed
    (Subgroup.normalizer (factor : Set GroupType)) localFixed_normalized
    (normalizer_normalized actor factor datum.factor_compatible.1)
  have witness_le : witness ≤ parent := (Subgroup.map_subtype_le _).trans (localCore_le.trans inf_le_left)
  have centralizes : witness ≤ Subgroup.centralizer (localFactor : Set GroupType) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp commutator_trivial
  have trap := incomplete_abelian_hall_product_subgroup_normalizer_trap localFactor datum abelian
    inf_le_left localFactor_nontrivial localFactor_normalized
  have witness_normalizes : witness ≤ Subgroup.normalizer (factor : Set GroupType) :=
    (le_inf witness_le (centralizes.trans (Subgroup.centralizer_le_normalizer _))).trans trap.2
  obtain ⟨fixedSylow, fixedSylow_equal⟩ := normalized_sylow_centralizer_intersection prime kernelPrime
    datum.prime_prime kernelPrime_prime actor localCore actor_pgroup localCore_normalized
    (parent_coprime.of_dvd_right (Subgroup.card_dvd_of_le (localCore_le.trans inf_le_left))) sylow sylow_normalized
  let fixedCore := localCore ⊓ Subgroup.centralizer (actor : Set GroupType)
  have fixedSylow_control : (fixedSylow : Subgroup fixedCore).map fixedCore.subtype ≤ control := by
    rw [fixedSylow_equal]
    exact le_inf (le_inf (inf_le_left.trans witness_le) inf_le_right) (inf_le_left.trans witness_normalizes)
  have fixedCore_le_common : fixedCore ≤ common := inf_le_inf_right _ (localCore_le.trans inf_le_left)
  have fixedCore_index := sylow_containment_relIndex_coprime kernelPrime kernelPrime_prime fixedCore control
    fixedSylow fixedSylow_control
  have local_product := incomplete_abelian_hall_product_local_normalizer_product fixedActor selected datum abelian
    fixedActor_le selected_member selected_le
  have common_product : subgroupProduct fixedCore control = (common : Set GroupType) := by
    have product := normalized_product_fixed_points prime datum.prime_prime actor localFixed localCore localNormalizer
      actor_pgroup localFixed_normalized localCore_normalized localNormalizer_normalized localCore_le inf_le_left
      (parent_coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)) local_product
    have fixed_equal : localFixed ⊓ Subgroup.centralizer (actor : Set GroupType) = common := by
      apply le_antisymm (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      exact le_inf (inf_le_inf_left _ (Subgroup.centralizer_le fixedActor_le)) inf_le_right
    have normalizer_equal : localNormalizer ⊓ Subgroup.centralizer (actor : Set GroupType) = control := by
      change (localFixed ⊓ Subgroup.normalizer (factor : Set GroupType)) ⊓
        Subgroup.centralizer (actor : Set GroupType) = _
      rw [inf_right_comm, fixed_equal]
    rw [fixed_equal, normalizer_equal] at product
    exact product
  have common_index : Nat.Coprime kernelPrime (control.relIndex common) := by
    rw [subgroup_product_relIndex common fixedCore control fixedCore_le_common inf_le_left common_product]
    exact fixedCore_index
  let _commonCharacteristic := prime_set_core_characteristic (GroupType := common) ({groupPrime}ᶜ)
  have commonCore_le : commonCore ≤ common := Subgroup.map_subtype_le _
  have common_normalizes_core : common ≤ Subgroup.normalizer (commonCore : Set GroupType) :=
    characteristic_subgroup_map_normalized common common Subgroup.le_normalizer _
  have core_index : Nat.Coprime kernelPrime (control.relIndex commonCore) :=
    common_index.of_dvd_right (normalizing_subgroup_relIndex_dvd common commonCore control commonCore_le
      inf_le_left (inf_le_left.trans common_normalizes_core))
  obtain ⟨commonSylow, commonSylow_control⟩ := sylow_exists_le_of_relIndex_coprime kernelPrime kernelPrime_prime
    commonCore control core_index
  exact incomplete_abelian_hall_product_fixed_core_sylow_escape kernel datum abelian common_le_parent kernel_le
    kernel_nontrivial kernel_normal kernel_normalized common_normalized kernelPrime kernelPrime_prime kernelPrime_spectrum
    kernelPrime_distinct kernel_coprime commonSylow (commonSylow_control.trans inf_le_right)

end CFSG.SignalizerFunctor.Helpers
