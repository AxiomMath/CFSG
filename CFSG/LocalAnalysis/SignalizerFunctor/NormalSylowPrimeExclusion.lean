module

public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleConjugation

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem normal_subgroup_coprime_of_sylow_inf_bot (prime : ℕ) (prime_prime : prime.Prime)
    (normal : Subgroup GroupType) [normal.Normal] (sylow : Sylow prime GroupType)
    (trivial : normal ⊓ (sylow : Subgroup GroupType) = ⊥) : Nat.Coprime prime (Nat.card normal) := by
  classical
  let : Fact prime.Prime := ⟨prime_prime⟩
  let internalSylow : Sylow prime normal := Classical.choice inferInstance
  let embedded := (internalSylow : Subgroup normal).map normal.subtype
  have embedded_pgroup : IsPGroup prime embedded := internalSylow.isPGroup'.map normal.subtype
  obtain ⟨ambientSylow, embedded_le⟩ := embedded_pgroup.exists_le_sylow
  obtain ⟨conjugator, conjugates⟩ := MulAction.exists_smul_eq GroupType ambientSylow sylow
  have ambient_eq : conjugateSubgroup conjugator (ambientSylow : Subgroup GroupType) = sylow :=
    congrArg (fun result : Sylow prime GroupType => (result : Subgroup GroupType)) conjugates
  have conjugated_le : conjugateSubgroup conjugator embedded ≤ (sylow : Subgroup GroupType) := by
    have mapped := Subgroup.map_mono (f := (MulAut.conj conjugator).toMonoidHom) embedded_le
    change conjugateSubgroup conjugator embedded ≤ conjugateSubgroup conjugator (ambientSylow : Subgroup GroupType)
      at mapped
    rwa [ambient_eq] at mapped
  have conjugated_normal : conjugateSubgroup conjugator embedded ≤ normal := by
    rintro _ ⟨original, member, rfl⟩
    exact Subgroup.Normal.conj_mem (inferInstance : normal.Normal) original
      ((Subgroup.map_subtype_le _) member) conjugator
  have conjugated_bot : conjugateSubgroup conjugator embedded = ⊥ :=
    le_bot_iff.mp ((le_inf conjugated_normal conjugated_le).trans trivial.le)
  have embedded_bot : embedded = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj conjugator).injective).mp conjugated_bot
  have internal_bot : (internalSylow : Subgroup normal) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ normal.subtype_injective).mp embedded_bot
  have index_prime := internalSylow.not_dvd_index
  rw [internal_bot, Subgroup.index_bot] at index_prime
  exact prime_prime.coprime_iff_not_dvd.mpr index_prime

omit [Finite GroupType] in
theorem normalizer_normalizes_centralizer (actor target : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    actor ≤ Subgroup.normalizer (Subgroup.centralizer (target : Set GroupType) : Set GroupType) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator conjugator_member element member
  apply Subgroup.mem_centralizer_iff.mpr
  intro targetElement target_member
  have inverse_member := Subgroup.le_normalizer_iff.mp normalized conjugator⁻¹
    (actor.inv_mem conjugator_member) targetElement target_member
  have commute := Subgroup.mem_centralizer_iff.mp member _ inverse_member
  have multiplied := congrArg (fun original : GroupType => conjugator * original * conjugator⁻¹) commute
  simpa only [inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel_right,
    mul_inv_cancel, mul_one] using multiplied

end CFSG.SignalizerFunctor.Helpers
