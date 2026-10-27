module

public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleProductCentralizers

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem normal_core_map_automorphism (subgroup : Subgroup GroupType) (equivalence : GroupType ≃* GroupType) :
    subgroup.normalCore.map equivalence.toMonoidHom = (subgroup.map equivalence.toMonoidHom).normalCore := by
  have map_le : ∀ candidate : Subgroup GroupType, ∀ isomorphism : GroupType ≃* GroupType,
      candidate.normalCore.map isomorphism.toMonoidHom ≤ (candidate.map isomorphism.toMonoidHom).normalCore := by
    intro candidate isomorphism
    let _normal := (inferInstance : candidate.normalCore.Normal).map isomorphism.toMonoidHom isomorphism.surjective
    exact Subgroup.normal_le_normalCore.mpr (Subgroup.map_mono candidate.normalCore_le)
  apply le_antisymm (map_le subgroup equivalence)
  have inverse_le := Subgroup.map_mono (f := equivalence.toMonoidHom)
    (map_le (subgroup.map equivalence.toMonoidHom) equivalence.symm)
  have identity_first : equivalence.symm.toMonoidHom.comp equivalence.toMonoidHom = MonoidHom.id GroupType := by
    ext element
    exact equivalence.symm_apply_apply element
  have identity_second : equivalence.toMonoidHom.comp equivalence.symm.toMonoidHom = MonoidHom.id GroupType := by
    ext element
    exact equivalence.apply_symm_apply element
  simp only [Subgroup.map_map, identity_first, Subgroup.map_id, identity_second,
    Subgroup.map_id] at inverse_le
  exact inverse_le

omit [Finite GroupType] in
theorem normal_core_normalized (actor subgroup : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (subgroup : Set GroupType)) :
    actor ≤ Subgroup.normalizer (subgroup.normalCore : Set GroupType) := by
  intro element member
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change subgroup.normalCore.map (MulAut.conj element).toMonoidHom = subgroup.normalCore
  have subgroup_eq : subgroup.map (MulAut.conj element).toMonoidHom = subgroup :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (normalized member)
  rw [normal_core_map_automorphism subgroup (MulAut.conj element), subgroup_eq]

theorem incomplete_full_centralizers_normal_compatible_trivial
    (prime rank : ℕ) (prime_prime : prime.Prime) (actor target : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType) (coprime : Nat.Coprime prime (Nat.card GroupType))
    (full : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected = Subgroup.centralizer (selected : Set GroupType))
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (incomplete : ¬ solvableSignalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected))
    (compatible : solvableSignalizerCompatible prime rank actor values target) [target.Normal] : target = ⊥ := by
  by_contra nontrivial
  have complete := full_centralizers_locally_complete_normalizer_solvable prime rank prime_prime actor target
    elementary large values coprime full locally_complete compatible nontrivial
  rw [Subgroup.normalizer_eq_top] at complete
  have completion_top := full_centralizers_completion_eq_top prime rank prime_prime actor elementary large
    values coprime full
  apply incomplete
  rwa [completion_top]

theorem incomplete_full_centralizers_compatible_normal_core_trivial
    (prime rank : ℕ) (prime_prime : prime.Prime) (actor target : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType) (coprime : Nat.Coprime prime (Nat.card GroupType))
    (full : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected = Subgroup.centralizer (selected : Set GroupType))
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (incomplete : ¬ solvableSignalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected))
    (compatible : solvableSignalizerCompatible prime rank actor values target) : target.normalCore = ⊥ := by
  have core_compatible := solvable_signalizer_compatible_of_le prime rank actor values target target.normalCore
    compatible target.normalCore_le (normal_core_normalized actor target compatible.1.1)
  exact incomplete_full_centralizers_normal_compatible_trivial prime rank prime_prime actor target.normalCore
    elementary large values coprime full locally_complete incomplete core_compatible

end CFSG.SignalizerFunctor.Helpers
