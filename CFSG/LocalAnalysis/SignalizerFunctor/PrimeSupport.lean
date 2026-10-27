module

public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleSubgroups

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

open scoped Pointwise

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem invariant_prime_subgroup_detected_by_fixed_points
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime)
    (groupPrime_prime : groupPrime.Prime)
    (actor target : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (target_normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (target_coprime : Nat.Coprime prime (Nat.card target))
    (target_pgroup : IsPGroup groupPrime target) (nontrivial : target ≠ ⊥) :
    ∃ subgroup ∈ signalizerFunctorEk prime rank actor,
      groupPrime ∣ Nat.card (target ⊓ Subgroup.centralizer (subgroup : Set GroupType) :
        Subgroup GroupType) := by
  classical
  let : Fact groupPrime.Prime := ⟨groupPrime_prime⟩
  have generated := elementary_abelian_centralizer_generation prime rank prime_prime actor
    target elementary large target_normalized target_coprime
  have fixed_nontrivial : ∃ subgroup ∈ signalizerFunctorEk prime rank actor,
      target ⊓ Subgroup.centralizer (subgroup : Set GroupType) ≠ ⊥ := by
    by_contra! all_trivial
    apply nontrivial
    rw [← generated]
    apply iSup_eq_bot.mpr
    intro subgroup
    exact iSup_eq_bot.mpr (all_trivial subgroup)
  obtain ⟨subgroup, member, fixed_nontrivial⟩ := fixed_nontrivial
  have fixed_pgroup := target_pgroup.to_le
    (show target ⊓ Subgroup.centralizer (subgroup : Set GroupType) ≤ target from inf_le_left)
  refine ⟨subgroup, member, ?_⟩
  rcases fixed_pgroup.card_eq_or_dvd with cardinality | divides
  · exact (fixed_nontrivial ((Subgroup.eq_bot_iff_card _).mpr cardinality)).elim
  · exact divides

theorem signalizer_compatible_prime_support
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime)
    (groupPrime_prime : groupPrime.Prime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (values_coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (target : Subgroup GroupType)
    (compatible : signalizerCompatible prime rank actor values target)
    (divides : groupPrime ∣ Nat.card target) :
    ∃ subgroup ∈ signalizerFunctorEk prime rank actor,
      groupPrime ∣ Nat.card (values subgroup) := by
  classical
  have rank_large : prime ^ rank ≤ Nat.card actor := by
    apply le_trans _ large
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ prime_prime.pos
  have target_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary
    rank_large values values_coprime target compatible.1 compatible.2
  let _action := conjugationAction actor target compatible.1
  obtain ⟨sylow, fixed⟩ := invariant_sylow_exists prime groupPrime prime_prime groupPrime_prime
    (elementary_abelian_isPGroup prime actor elementary) target_coprime
  let embedded := (sylow : Subgroup target).map target.subtype
  have embedded_le : embedded ≤ target := Subgroup.map_subtype_le _
  have embedded_pgroup : IsPGroup groupPrime embedded := sylow.isPGroup'.map target.subtype
  have embedded_coprime : Nat.Coprime prime (Nat.card embedded) :=
    target_coprime.of_dvd_right (Subgroup.card_dvd_of_le embedded_le)
  have embedded_normalized : actor ≤ Subgroup.normalizer (embedded : Set GroupType) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro actorElement actor_member element member
    obtain ⟨representative, representative_member, rfl⟩ := member
    have image_fixed : (⟨actorElement, actor_member⟩ : actor) •
        (sylow : Subgroup target) = sylow := by
      rw [← Sylow.pointwise_smul_def, fixed]
    refine ⟨(⟨actorElement, actor_member⟩ : actor) • representative, ?_, rfl⟩
    rw [← image_fixed]
    exact Subgroup.smul_mem_pointwise_smul representative
      (⟨actorElement, actor_member⟩ : actor) _ representative_member
  have embedded_nontrivial : embedded ≠ ⊥ := by
    intro trivial
    have cardinality := (Subgroup.eq_bot_iff_card embedded).mp trivial
    change Nat.card ((sylow : Subgroup target).map target.subtype) = 1 at cardinality
    rw [Subgroup.card_map_of_injective target.subtype_injective] at cardinality
    let : Fact groupPrime.Prime := ⟨groupPrime_prime⟩
    have sylow_divides : groupPrime ∣ Nat.card (sylow : Subgroup target) := by
      simpa using sylow.pow_dvd_card_of_pow_dvd_card (n := 1) (by simpa using divides)
    rw [cardinality] at sylow_divides
    exact groupPrime_prime.not_dvd_one sylow_divides
  obtain ⟨subgroup, member, fixed_divides⟩ := invariant_prime_subgroup_detected_by_fixed_points
    prime rank groupPrime prime_prime groupPrime_prime actor embedded elementary large
      embedded_normalized embedded_coprime embedded_pgroup embedded_nontrivial
  refine ⟨subgroup, member, fixed_divides.trans (Subgroup.card_dvd_of_le ?_)⟩
  exact (inf_le_inf_right _ embedded_le).trans (compatible.2 subgroup member)

end CFSG.SignalizerFunctor.Helpers
