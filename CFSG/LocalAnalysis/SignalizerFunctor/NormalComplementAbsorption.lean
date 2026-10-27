module

public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageCore

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem normal_complement_absorption (prime : ℕ) (prime_prime : prime.Prime)
    (first second : Subgroup GroupType)
    (first_coprime : Nat.Coprime prime (Nat.card first))
    (normalizes : second ≤ Subgroup.normalizer (first : Set GroupType))
    (whole : (primeSetCore (GroupType := GroupType) ({prime}ᶜ) ⊔ first) ⊔ second = ⊤) :
    first ≤ primeSetCore (GroupType := GroupType) ({prime}ᶜ) ∧
      primeSetCore (GroupType := GroupType) ({prime}ᶜ) ⊔ second = ⊤ := by
  let core := primeSetCore (GroupType := GroupType) ({prime}ᶜ)
  let _normalCore := prime_set_core_normal (GroupType := GroupType) ({prime}ᶜ)
  have second_normalizes : second ≤ Subgroup.normalizer ((core ⊔ first : Subgroup GroupType) : Set GroupType) :=
    (le_inf (by rw [Subgroup.normalizer_eq_top]; exact le_top) normalizes).trans
      (Subgroup.inf_normalizer_le_normalizer_sup core first)
  have normalizer_whole : Subgroup.normalizer ((core ⊔ first : Subgroup GroupType) : Set GroupType) = ⊤ := by
    apply top_unique
    rw [← whole]
    exact sup_le Subgroup.le_normalizer second_normalizes
  have combined_normal : (core ⊔ first : Subgroup GroupType).Normal :=
    Subgroup.normalizer_eq_top_iff.mp normalizer_whole
  have combined_supported : primeSupported ({prime}ᶜ) (Nat.card (core ⊔ first : Subgroup GroupType)) :=
    prime_supported_sup_of_normalizing ({prime}ᶜ) core first
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
      (prime_set_core_supported ({prime}ᶜ))
      ((prime_supported_complement_singleton_iff_coprime prime prime_prime _).mpr first_coprime)
  have combined_le : core ⊔ first ≤ core :=
    prime_set_core_contains ({prime}ᶜ) (core ⊔ first) combined_normal combined_supported
  have first_le := le_sup_right.trans combined_le
  change (core ⊔ first) ⊔ second = ⊤ at whole
  exact ⟨first_le, by simpa only [sup_eq_left.mpr first_le] using whole⟩

theorem ambient_normal_complement_absorption (prime : ℕ) (prime_prime : prime.Prime)
    (parent first second : Subgroup GroupType)
    (first_le : first ≤ parent) (second_le : second ≤ parent)
    (first_coprime : Nat.Coprime prime (Nat.card first))
    (normalizes : second ≤ Subgroup.normalizer (first : Set GroupType))
    (whole :
      ((primeSetCore (GroupType := parent) ({prime}ᶜ)).map parent.subtype ⊔ first) ⊔ second = parent) :
    first ≤ (primeSetCore (GroupType := parent) ({prime}ᶜ)).map parent.subtype ∧
      (primeSetCore (GroupType := parent) ({prime}ᶜ)).map parent.subtype ⊔ second = parent := by
  let internalCore := primeSetCore (GroupType := parent) ({prime}ᶜ)
  have internal_coprime : Nat.Coprime prime (Nat.card (first.subgroupOf parent)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe first_le).toEquiv]
    exact first_coprime
  have internal_normalizes : second.subgroupOf parent ≤
      Subgroup.normalizer (first.subgroupOf parent : Set parent) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro secondElement second_member firstElement first_member
    exact Subgroup.le_normalizer_iff.mp normalizes secondElement.val second_member
      firstElement.val first_member
  have internal_whole :
      (internalCore ⊔ first.subgroupOf parent) ⊔ second.subgroupOf parent = ⊤ := by
    apply Subgroup.map_injective parent.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le first_le,
      Subgroup.map_subgroupOf_eq_of_le second_le, ← MonoidHom.range_eq_map, parent.subtype_range]
    exact whole
  obtain ⟨internal_le, internal_eq⟩ := normal_complement_absorption prime prime_prime
    (first.subgroupOf parent) (second.subgroupOf parent)
    internal_coprime internal_normalizes internal_whole
  have mapped_le := Subgroup.map_mono (f := parent.subtype) internal_le
  rw [Subgroup.map_subgroupOf_eq_of_le first_le] at mapped_le
  have mapped_eq := congrArg (Subgroup.map parent.subtype) internal_eq
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le second_le,
    ← MonoidHom.range_eq_map, parent.subtype_range] at mapped_eq
  exact ⟨mapped_le, mapped_eq⟩

end CFSG.SignalizerFunctor.Helpers
