module

public import CFSG.LocalAnalysis.SignalizerFunctor.NormalSylowPrimeExclusion
public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductWeakClosureSylow
public import CFSG.LocalAnalysis.SignalizerFunctor.WeakClosureConjugation

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem generated_fixed_subgroup_escape (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor target control : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card target)) (escape : ¬ target ≤ control) :
    ∃ selected ∈ signalizerFunctorEk prime rank actor,
      ¬ target ⊓ Subgroup.centralizer (selected : Set GroupType) ≤ control := by
  classical
  by_contra no_witness
  apply escape
  rw [← elementary_abelian_centralizer_generation prime rank prime_prime actor target elementary large normalized coprime]
  apply iSup_le
  intro selected
  apply iSup_le
  intro member
  by_contra outside
  exact no_witness ⟨selected, member, outside⟩

omit [Finite GroupType] in
theorem fixed_conjugate_subgroup_centralizes (actor fixedActor target : Subgroup GroupType)
    (fixedActor_le : fixedActor ≤ actor) (target_central : target ≤ Subgroup.centralizer (fixedActor : Set GroupType))
    (element : GroupType) (element_fixed : element ∈ Subgroup.centralizer (actor : Set GroupType)) :
    conjugateSubgroup element target ≤ Subgroup.centralizer (fixedActor : Set GroupType) := by
  have centralizer_normalized := normalizer_normalizes_centralizer (Subgroup.centralizer (actor : Set GroupType)) fixedActor
    ((Subgroup.centralizer_le fixedActor_le).trans (Subgroup.centralizer_le_normalizer _))
  exact (Subgroup.map_mono (f := (MulAut.conj element).toMonoidHom) target_central).trans
    (normalized_conjugate_subgroup_le _ _ centralizer_normalized element element_fixed)

omit [Finite GroupType] in
theorem fixed_conjugate_subgroup_normalized (actor target : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (element : GroupType) (element_fixed : element ∈ Subgroup.centralizer (actor : Set GroupType)) :
    actor ≤ Subgroup.normalizer (conjugateSubgroup element target : Set GroupType) := by
  have actor_preserved : conjugateSubgroup element actor = actor := by
    have normalizes := (Subgroup.centralizer_le_normalizer (actor : Set GroupType)) element_fixed
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp normalizes
  have transported := conjugate_subgroup_normalizes actor target element normalized
  rwa [actor_preserved] at transported

variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_abelian_hall_product_weak_closure_contradiction (kernel : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (kernelPrime : ℕ) (kernelPrime_prime : kernelPrime.Prime) (kernelPrime_distinct : kernelPrime ≠ groupPrime)
    (kernel_le : kernel ≤ complement) (kernel_nontrivial : kernel ≠ ⊥) (kernel_pgroup : IsPGroup kernelPrime kernel)
    (kernel_normal : (kernel.subgroupOf complement).Normal)
    (kernel_normalized : actor ≤ Subgroup.normalizer (kernel : Set GroupType))
    (intersections : ∀ selected ∈ signalizerFunctorEk prime (rank + 1) actor,
      factor ⊓ Subgroup.centralizer (selected : Set GroupType) ≠ ⊥ →
      kernel ≤ conjugateIntersection (factor ⊓ Subgroup.centralizer (selected : Set GroupType)) complement) : False := by
  classical
  have parent_coprime := incomplete_hall_product_parent_coprime datum
  have factor_coprime := parent_coprime.of_dvd_right (Subgroup.card_dvd_of_le datum.factor_le)
  have actor_pgroup := elementary_abelian_isPGroup prime actor datum.elementary
  have first_escape : ¬ factor ≤ (⊥ : Subgroup GroupType) := fun contained =>
    incomplete_hall_product_factor_nontrivial datum (le_bot_iff.mp contained)
  obtain ⟨firstActor, first_member, first_nontrivial⟩ := generated_fixed_subgroup_escape prime (rank + 1) datum.prime_prime
    actor factor ⊥ datum.elementary (by simpa only [Nat.add_assoc] using large) datum.factor_compatible.1 factor_coprime first_escape
  have first_nontrivial' : factor ⊓ Subgroup.centralizer (firstActor : Set GroupType) ≠ ⊥ :=
    fun equal => first_nontrivial equal.le
  obtain ⟨sylow, kernel_target, target_normalized, weak_nontrivial, weak_normalized, _, local_compatible, localFactorSylow,
    localFactorSylow_equal⟩ := incomplete_abelian_hall_product_weak_closure_sylow firstActor kernel datum abelian
      first_member.1 first_nontrivial' kernelPrime kernelPrime_prime kernelPrime_distinct kernel_le kernel_nontrivial kernel_pgroup
      kernel_normal kernel_normalized (intersections firstActor first_member first_nontrivial')
  let target := (sylow : Subgroup parent).map parent.subtype
  let weak := relativeWeakClosure parent kernel target
  let localParent := parent ⊓ Subgroup.normalizer (weak : Set GroupType)
  have weak_prime : IsPGroup kernelPrime weak := (sylow.isPGroup'.map parent.subtype).to_le
    (relative_weak_closure_le parent kernel target)
  have weak_coprime := prime_coprime_pgroup_card groupPrime kernelPrime datum.groupPrime_prime kernelPrime_prime
    kernelPrime_distinct.symm weak_prime
  have factor_escape : ¬ factor ≤ localParent := by
    intro contained
    have weak_trivial := incomplete_hall_product_normalized_complement_trivial weak datum
      ((relative_weak_closure_le parent kernel target).trans (Subgroup.map_subtype_le _)) weak_coprime
      (contained.trans inf_le_right)
    exact weak_nontrivial weak_trivial
  obtain ⟨secondActor, second_member, second_escape⟩ := generated_fixed_subgroup_escape prime (rank + 1) datum.prime_prime
    actor factor localParent datum.elementary (by simpa only [Nat.add_assoc] using large) datum.factor_compatible.1
    factor_coprime factor_escape
  let secondFactor := factor ⊓ Subgroup.centralizer (secondActor : Set GroupType)
  have second_nontrivial : secondFactor ≠ ⊥ := fun equal => second_escape (equal.le.trans bot_le)
  obtain ⟨secondSylow, _, secondSylow_normalized, _, _, secondWeak_factor, _, _⟩ :=
    incomplete_abelian_hall_product_weak_closure_sylow secondActor kernel datum abelian second_member.1 second_nontrivial
      kernelPrime kernelPrime_prime kernelPrime_distinct kernel_le kernel_nontrivial kernel_pgroup kernel_normal kernel_normalized
      (intersections secondActor second_member second_nontrivial)
  let secondTarget := (secondSylow : Subgroup parent).map parent.subtype
  let secondWeak := relativeWeakClosure parent kernel secondTarget
  obtain ⟨conjugator, conjugator_member, conjugates⟩ := normalized_sylows_conjugate_by_common_fixed prime kernelPrime
    datum.prime_prime kernelPrime_prime actor parent actor_pgroup datum.parent_normalized parent_coprime secondSylow sylow
    secondSylow_normalized target_normalized
  have weak_conjugates : conjugateSubgroup conjugator secondWeak = weak := by
    rw [relative_weak_closure_conjugate parent kernel secondTarget conjugator conjugator_member.1, conjugates]
  have secondFactor_conjugate_le : conjugateSubgroup conjugator secondFactor ≤ localParent := by
    have transported := conjugate_subgroup_normalizes secondFactor secondWeak conjugator secondWeak_factor
    rw [weak_conjugates] at transported
    have parent_le : conjugateSubgroup conjugator secondFactor ≤ parent := by
      exact (Subgroup.map_mono (f := (MulAut.conj conjugator).toMonoidHom)
        (show secondFactor ≤ parent from inf_le_left.trans datum.factor_le)).trans
          (normalized_conjugate_subgroup_le parent parent Subgroup.le_normalizer conjugator conjugator_member.1)
    exact le_inf parent_le transported
  have secondFactor_normalized : actor ≤ Subgroup.normalizer (secondFactor : Set GroupType) :=
    normalizer_inf_of_le actor factor (Subgroup.centralizer (secondActor : Set GroupType)) datum.factor_compatible.1
      ((elementary_abelian_le_centralizer prime actor secondActor datum.elementary second_member.1).trans Subgroup.le_normalizer)
  have conjugate_normalized := fixed_conjugate_subgroup_normalized actor secondFactor secondFactor_normalized conjugator
    conjugator_member.2
  have conjugate_prime : IsPGroup groupPrime (conjugateSubgroup conjugator secondFactor) :=
    (datum.factor_pgroup.to_le inf_le_left).map (MulAut.conj conjugator).toMonoidHom
  obtain ⟨localSylow, conjugate_contains, localSylow_normalized⟩ := normalized_pgroup_actor_sylow_containing prime groupPrime
    datum.prime_prime datum.groupPrime_prime actor localParent (conjugateSubgroup conjugator secondFactor) actor_pgroup
    local_compatible.1.1 (parent_coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)) secondFactor_conjugate_le
    conjugate_prime conjugate_normalized
  have localFactorSylow_normalized : actor ≤ Subgroup.normalizer
      (((localFactorSylow : Subgroup localParent).map localParent.subtype : Subgroup GroupType) : Set GroupType) := by
    rw [localFactorSylow_equal]
    exact normalizer_inf_of_le actor localParent factor local_compatible.1.1 datum.factor_compatible.1
  obtain ⟨secondConjugator, secondConjugator_member, local_conjugates⟩ := normalized_sylows_conjugate_by_common_fixed
    prime groupPrime datum.prime_prime datum.groupPrime_prime actor localParent actor_pgroup local_compatible.1.1
    (parent_coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)) localSylow localFactorSylow
      localSylow_normalized localFactorSylow_normalized
  let combined := secondConjugator * conjugator
  have combined_fixed : combined ∈ Subgroup.centralizer (actor : Set GroupType) :=
    (Subgroup.centralizer (actor : Set GroupType)).mul_mem secondConjugator_member.2 conjugator_member.2
  have combined_factor : conjugateSubgroup combined secondFactor ≤ localParent ⊓ factor := by
    have mapped := Subgroup.map_mono (f := (MulAut.conj secondConjugator).toMonoidHom) conjugate_contains
    change conjugateSubgroup secondConjugator (conjugateSubgroup conjugator secondFactor) ≤
      conjugateSubgroup secondConjugator ((localSylow : Subgroup localParent).map localParent.subtype) at mapped
    rw [conjugate_subgroup_mul, local_conjugates, localFactorSylow_equal] at mapped
    exact mapped
  have combined_second : conjugateSubgroup combined secondFactor ≤ secondFactor := le_inf
    (combined_factor.trans inf_le_right)
    (fixed_conjugate_subgroup_centralizes actor secondActor secondFactor second_member.1 inf_le_right combined combined_fixed)
  have equal : conjugateSubgroup combined secondFactor = secondFactor := Subgroup.eq_of_le_of_card_ge combined_second
    (by rw [conjugate_subgroup_card])
  exact second_escape (equal.symm.le.trans (combined_factor.trans inf_le_left))

end CFSG.SignalizerFunctor.Helpers
