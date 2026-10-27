module

public import CFSG.LocalAnalysis.SignalizerFunctor.JointInvariantSylow
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvableRelativeMatsuyama
public import CFSG.LocalAnalysis.SignalizerFunctor.MaximalInvariantWeakClosure
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalizedSylowContainment

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_abelian_hall_product_weak_closure_sylow (fixedActor kernel : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (fixedActor_le : fixedActor ≤ actor)
    (localFactor_nontrivial : factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType) ≠ ⊥)
    (kernelPrime : ℕ) (kernelPrime_prime : kernelPrime.Prime) (kernelPrime_distinct : kernelPrime ≠ groupPrime)
    (kernel_le : kernel ≤ complement) (kernel_nontrivial : kernel ≠ ⊥) (kernel_pgroup : IsPGroup kernelPrime kernel)
    (kernel_normal : (kernel.subgroupOf complement).Normal)
    (kernel_normalized : actor ≤ Subgroup.normalizer (kernel : Set GroupType))
    (kernel_intersection : kernel ≤ conjugateIntersection
      (factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)) complement) :
    ∃ sylow : Sylow kernelPrime parent,
      let target := (sylow : Subgroup parent).map parent.subtype
      let weak := relativeWeakClosure parent kernel target
      let localParent := parent ⊓ Subgroup.normalizer (weak : Set GroupType)
      kernel ≤ target ∧ actor ≤ Subgroup.normalizer (target : Set GroupType) ∧ weak ≠ ⊥ ∧
      actor ≤ Subgroup.normalizer (weak : Set GroupType) ∧
      factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType) ≤ Subgroup.normalizer (weak : Set GroupType) ∧
      solvableSignalizerCompatible prime rank actor values localParent ∧
      (∃ localSylow : Sylow groupPrime localParent,
        (localSylow : Subgroup localParent).map localParent.subtype = localParent ⊓ factor) := by
  classical
  let localFactor := factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  have localFactor_le : localFactor ≤ parent := inf_le_left.trans datum.factor_le
  have localFactor_normalized : actor ≤ Subgroup.normalizer (localFactor : Set GroupType) :=
    normalizer_inf_of_le actor factor (Subgroup.centralizer (fixedActor : Set GroupType)) datum.factor_compatible.1
      ((elementary_abelian_le_centralizer prime actor fixedActor datum.elementary fixedActor_le).trans Subgroup.le_normalizer)
  obtain ⟨weak, weak_prime, weak_actor, weak_factor, kernel_weak, weak_parent, weak_closed, maximal⟩ :=
    maximal_invariant_relative_weak_closure kernelPrime kernelPrime_prime actor parent complement localFactor kernel
      kernel_le datum.complement_le kernel_pgroup kernel_normal kernel_normalized localFactor_le localFactor_normalized
      kernel_intersection
  let localParent := parent ⊓ Subgroup.normalizer (weak : Set GroupType)
  have weak_nontrivial : weak ≠ ⊥ := fun trivial => kernel_nontrivial (le_bot_iff.mp (kernel_weak.trans trivial.le))
  have weak_compatible : solvableSignalizerCompatible prime rank actor values weak := by
    let : Fact kernelPrime.Prime := ⟨kernelPrime_prime⟩
    let _nilpotent := weak_prime.isNilpotent
    exact ⟨incomplete_hall_product_normalized_compatible weak datum weak_parent weak_actor, inferInstance⟩
  have local_compatible := incomplete_hall_product_normalizer_compatible weak datum weak_compatible weak_nontrivial
  have local_normalized := local_compatible.1.1
  have local_solvable := local_compatible.2
  have weak_local : weak ≤ localParent := le_inf weak_parent Subgroup.le_normalizer
  have localFactor_local : localFactor ≤ localParent := le_inf localFactor_le weak_factor
  have local_factor_nontrivial : localParent ⊓ factor ≠ ⊥ := by
    intro trivial
    exact localFactor_nontrivial (le_bot_iff.mp ((le_inf localFactor_local inf_le_left).trans trivial.le))
  obtain ⟨localFactorSylow, localFactorSylow_equal⟩ := incomplete_abelian_hall_product_sylow_intersection localParent datum
    abelian inf_le_left local_normalized local_factor_nontrivial
  have localFactorSylow_embedded : (localFactorSylow : Subgroup localParent).map localParent.subtype = localParent ⊓ factor := by
    rw [localFactorSylow_equal, Subgroup.subgroupOf_map_subtype, inf_comm]
  let core := (primeSetCore (GroupType := localParent) ({groupPrime}ᶜ)).map localParent.subtype
  have absorbed := abelian_product_conjugates_le_local_core groupPrime kernelPrime datum.groupPrime_prime kernelPrime_prime
    kernelPrime_distinct parent complement factor kernel localParent weak kernel_le kernel_normal datum.whole abelian
    inf_le_left local_solvable weak_prime kernel_weak inf_le_right localFactorSylow
      (localFactorSylow_embedded.le.trans inf_le_right)
  have weak_core : weak ≤ core := weak_closed.symm.le.trans
    ((relative_weak_closure_mono parent kernel weak localParent weak_local).trans absorbed)
  let _coreCharacteristic := prime_set_core_characteristic (GroupType := localParent) ({groupPrime}ᶜ)
  have core_le_local : core ≤ localParent := Subgroup.map_subtype_le _
  have core_actor := characteristic_subgroup_map_normalized actor localParent local_normalized
    (primeSetCore (GroupType := localParent) ({groupPrime}ᶜ))
  have core_factor := characteristic_subgroup_map_normalized localFactor localParent
    (localFactor_local.trans Subgroup.le_normalizer) (primeSetCore (GroupType := localParent) ({groupPrime}ᶜ))
  have core_coprime : Nat.Coprime prime (Nat.card core) := (incomplete_hall_product_parent_coprime datum).of_dvd_right
    (Subgroup.card_dvd_of_le (core_le_local.trans inf_le_left))
  have core_second_coprime : Nat.Coprime groupPrime (Nat.card core) := by
    rw [Subgroup.card_map_of_injective localParent.subtype_injective]
    exact (prime_supported_complement_singleton_iff_coprime groupPrime datum.groupPrime_prime _).mp
      (prime_set_core_supported ({groupPrime}ᶜ))
  have core_solvable : Group.IsSolvable core := by
    let := local_solvable
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective core_le_local)
  have actor_prime := elementary_abelian_isPGroup prime actor datum.elementary
  obtain ⟨coreSylow, weak_coreSylow, coreSylow_actor, coreSylow_factor⟩ := jointly_normalized_sylow_containing
    prime groupPrime kernelPrime datum.prime_prime datum.groupPrime_prime kernelPrime_prime actor localFactor core weak
    actor_prime (datum.factor_pgroup.to_le inf_le_left) localFactor_normalized core_solvable core_coprime core_second_coprime
    core_actor core_factor weak_core weak_prime weak_actor weak_factor
  let coreTarget := (coreSylow : Subgroup core).map core.subtype
  have coreTarget_local : coreTarget ≤ localParent := (Subgroup.map_subtype_le _).trans core_le_local
  obtain ⟨localSylow, coreTarget_localSylow, localSylow_actor⟩ := normalized_pgroup_actor_sylow_containing prime kernelPrime
    datum.prime_prime kernelPrime_prime actor localParent coreTarget actor_prime local_normalized
    ((incomplete_hall_product_parent_coprime datum).of_dvd_right (Subgroup.card_dvd_of_le inf_le_left))
    coreTarget_local (coreSylow.isPGroup'.map core.subtype) coreSylow_actor
  let target := (localSylow : Subgroup localParent).map localParent.subtype
  have intersection_equal : target ⊓ core = coreTarget := embedded_normal_sylow_intersection kernelPrime kernelPrime_prime
    localParent core coreSylow localSylow coreTarget_localSylow
  let enlarged := relativeWeakClosure parent kernel coreTarget
  have weak_enlarged : weak ≤ enlarged := weak_closed.symm.le.trans
    (relative_weak_closure_mono parent kernel weak coreTarget weak_coreSylow)
  have enlarged_prime : IsPGroup kernelPrime enlarged := (coreSylow.isPGroup'.map core.subtype).to_le
    (relative_weak_closure_le parent kernel coreTarget)
  have enlarged_actor : actor ≤ Subgroup.normalizer (enlarged : Set GroupType) := relative_weak_closure_normalized
    actor parent kernel coreTarget datum.parent_normalized kernel_normalized coreSylow_actor
  have enlarged_factor : localFactor ≤ Subgroup.normalizer (enlarged : Set GroupType) :=
    (le_inf localFactor_le coreSylow_factor).trans (relative_weak_closure_parent_normalizer parent kernel coreTarget)
  have enlarged_parent : enlarged ≤ parent := (relative_weak_closure_le parent kernel coreTarget).trans
    (coreTarget_local.trans inf_le_left)
  have enlarged_equal : enlarged = weak := maximal enlarged enlarged_prime enlarged_actor enlarged_factor
    (kernel_weak.trans weak_enlarged) enlarged_parent (relative_weak_closure_idempotent parent kernel coreTarget) weak_enlarged
  have target_weak : relativeWeakClosure parent kernel target = weak := by
    apply le_antisymm
    · apply le_trans _ enlarged_equal.le
      apply iSup_le
      intro conjugator
      apply iSup_le
      intro contained
      have conjugate_local : conjugateSubgroup conjugator.val kernel ≤ localParent := contained.trans (Subgroup.map_subtype_le _)
      have conjugate_core : conjugateSubgroup conjugator.val kernel ≤ core :=
        (show conjugateSubgroup conjugator.val kernel ≤ relativeWeakClosure parent kernel localParent from
          le_iSup_of_le conjugator (le_iSup_of_le conjugate_local le_rfl)).trans absorbed
      have conjugate_target : conjugateSubgroup conjugator.val kernel ≤ coreTarget :=
        (le_inf contained conjugate_core).trans intersection_equal.le
      exact le_iSup_of_le conjugator (le_iSup_of_le conjugate_target le_rfl)
    · exact weak_closed.symm.le.trans (relative_weak_closure_mono parent kernel weak target
        (weak_coreSylow.trans coreTarget_localSylow))
  have target_normalizer : parent ⊓ Subgroup.normalizer (target : Set GroupType) ≤ localParent := by
    have weak_control := relative_weak_closure_parent_normalizer parent kernel target
    rw [target_weak] at weak_control
    exact le_inf inf_le_left weak_control
  obtain ⟨parentSylow, parentSylow_equal⟩ := parent_sylow_of_parent_normalizer_containment kernelPrime kernelPrime_prime
    parent localParent inf_le_left localSylow target_normalizer
  refine ⟨parentSylow, ?_⟩
  dsimp only
  rw [parentSylow_equal, target_weak]
  exact ⟨kernel_weak.trans (weak_coreSylow.trans coreTarget_localSylow), localSylow_actor, weak_nontrivial,
    weak_actor, weak_factor, local_compatible, localFactorSylow, localFactorSylow_embedded⟩

end CFSG.SignalizerFunctor.Helpers
