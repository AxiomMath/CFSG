module

public import CFSG.LocalAnalysis.SignalizerFunctor.SolvablePrimeCore

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType] [Group.IsSolvable GroupType]

theorem solvable_abelian_sylow_complement_commutator_le_core
    (prime : ℕ) (prime_prime : prime.Prime) (sylow : Sylow prime GroupType)
    (abelian : IsMulCommutative (sylow : Subgroup GroupType)) (actor target : Subgroup GroupType)
    (actor_le : actor ≤ (sylow : Subgroup GroupType))
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card target)) : ⁅target, actor⁆ ≤ primeSetCore ({prime}ᶜ) := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let complement := primeSetCore (GroupType := GroupType) ({prime}ᶜ)
  let _normal := prime_set_core_normal (GroupType := GroupType) ({prime}ᶜ)
  let projection := QuotientGroup.mk' complement
  let core := primeSetCore (GroupType := GroupType ⧸ complement) {prime}
  let _coreNormal := prime_set_core_normal (GroupType := GroupType ⧸ complement) {prime}
  have actor_image_le : actor.map projection ≤ core := by
    have sylow_image := solvable_abelian_sylow_quotient_eq_prime_core prime prime_prime sylow abelian
    exact (Subgroup.map_mono actor_le).trans sylow_image.le
  have image_le : (⁅target, actor⁆ : Subgroup GroupType).map projection ≤ core := by
    rw [Subgroup.map_commutator]
    exact (Subgroup.commutator_mono le_rfl actor_image_le).trans (Subgroup.commutator_le_right _ _)
  have commutator_le : ⁅target, actor⁆ ≤ target := commutator_le_of_normalizing target actor normalized
  have image_coprime : Nat.Coprime prime (Nat.card ((⁅target, actor⁆ : Subgroup GroupType).map projection)) :=
    (coprime.of_dvd_right (Subgroup.card_dvd_of_le commutator_le)).of_dvd_right
      (Subgroup.card_map_dvd _ projection)
  have image_pgroup : IsPGroup prime ((⁅target, actor⁆ : Subgroup GroupType).map projection) :=
    (prime_core_isPGroup (GroupType := GroupType ⧸ complement) prime prime_prime).to_le image_le
  have image_trivial : (⁅target, actor⁆ : Subgroup GroupType).map projection = ⊥ := by
    rcases image_pgroup.card_eq_or_dvd with cardinality | divides
    · exact (Subgroup.eq_bot_iff_card _).mpr cardinality
    · exact (prime_prime.coprime_iff_not_dvd.mp image_coprime divides).elim
  intro element member
  apply (QuotientGroup.eq_one_iff _).mp
  have mapped := Subgroup.mem_map_of_mem projection member
  rw [image_trivial] at mapped
  exact mapped

end CFSG.SignalizerFunctor.Helpers
