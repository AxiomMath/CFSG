module

public import CFSG.LocalAnalysis.SignalizerFunctor.ZJGrowthClassTwo

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

open scoped commutatorElement

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem pgroup_maximal_subgroup_normal (prime : ℕ) (prime_prime : prime.Prime)
    (pgroup : IsPGroup prime GroupType)
    (maximal : Subgroup GroupType) (coatom : IsCoatom maximal) : maximal.Normal := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let := pgroup.isNilpotent
  exact Subgroup.NormalizerCondition.normal_of_coatom maximal Group.normalizerCondition_of_isNilpotent coatom

theorem pgroup_maximal_subgroup_index (prime : ℕ) (prime_prime : prime.Prime)
    (pgroup : IsPGroup prime GroupType) (maximal : Subgroup GroupType) (coatom : IsCoatom maximal) :
    maximal.index = prime := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let _normal := pgroup_maximal_subgroup_normal prime prime_prime pgroup maximal coatom
  let projection := QuotientGroup.mk' maximal
  let _nontrivial : Nontrivial (GroupType ⧸ maximal) := QuotientGroup.nontrivial_iff.mpr coatom.ne_top
  have quotient_pgroup := pgroup.to_quotient maximal
  have divides : prime ∣ Nat.card (GroupType ⧸ maximal) := by
    rcases quotient_pgroup.card_eq_or_dvd with cardinality | divides
    · exact ((not_subsingleton (α := GroupType ⧸ maximal))
        (Nat.card_eq_one_iff_unique.mp cardinality).1).elim
    · exact divides
  obtain ⟨subgroup, subgroup_card⟩ := Sylow.exists_subgroup_card_pow_prime prime
    (n := 1) (by simpa only [pow_one] using divides)
  have preimage_contains : maximal ≤ subgroup.comap projection := by
    simpa only [projection, QuotientGroup.ker_mk'] using Subgroup.ker_le_comap projection subgroup
  have preimage_top : subgroup.comap projection = ⊤ := by
    by_contra not_top
    have equal := (coatom.ne_top_iff_eq preimage_contains).mp not_top
    have mapped := congrArg (Subgroup.map projection) equal
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective maximal)] at mapped
    have maximal_image : maximal.map projection = ⊥ := by
      apply (Subgroup.map_eq_bot_iff maximal).mpr
      dsimp only [projection]
      rw [QuotientGroup.ker_mk']
    rw [maximal_image] at mapped
    have cardinality := congrArg (fun target : Subgroup (GroupType ⧸ maximal) => Nat.card target) mapped
    rw [subgroup_card, Subgroup.card_bot, pow_one] at cardinality
    exact prime_prime.ne_one cardinality
  have subgroup_top : subgroup = ⊤ := by
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective maximal)
    simpa only [Subgroup.comap_top] using preimage_top
  rw [Subgroup.index_eq_card]
  rw [subgroup_top, Subgroup.card_top, pow_one] at subgroup_card
  exact subgroup_card

theorem pgroup_frattini_commutator_le (prime : ℕ) (prime_prime : prime.Prime)
    (pgroup : IsPGroup prime GroupType) : ⁅(⊤ : Subgroup GroupType), ⊤⁆ ≤ frattini GroupType := by
  intro element member
  change element ∈ ⨅ maximal ∈ {maximal : Subgroup GroupType | IsCoatom maximal}, maximal
  apply Subgroup.mem_iInf.mpr
  intro maximal
  apply Subgroup.mem_iInf.mpr
  intro coatom
  let : Fact prime.Prime := ⟨prime_prime⟩
  let _normal := pgroup_maximal_subgroup_normal prime prime_prime pgroup maximal coatom
  have quotient_card : Nat.card (GroupType ⧸ maximal) = prime := by
    rw [← Subgroup.index_eq_card]
    exact pgroup_maximal_subgroup_index prime prime_prime pgroup maximal coatom
  let _cyclic := isCyclic_of_prime_card quotient_card
  have quotient_centralizes : (⊤ : Subgroup GroupType) ≤ (Subgroup.centralizer
      ((⊤ : Subgroup GroupType).map (QuotientGroup.mk' maximal) : Set (GroupType ⧸ maximal))).comap
        (QuotientGroup.mk' maximal) := by
    intro target _
    apply Subgroup.mem_centralizer_iff.mpr
    intro other _
    exact mul_comm' other (QuotientGroup.mk' maximal target)
  exact quotient_centralizer_commutator_le ⊤ ⊤ maximal quotient_centralizes member

theorem pgroup_frattini_power_mem (prime : ℕ) (prime_prime : prime.Prime)
    (pgroup : IsPGroup prime GroupType) (element : GroupType) : element ^ prime ∈ frattini GroupType := by
  change element ^ prime ∈ ⨅ maximal ∈ {maximal : Subgroup GroupType | IsCoatom maximal}, maximal
  apply Subgroup.mem_iInf.mpr
  intro maximal
  apply Subgroup.mem_iInf.mpr
  intro coatom
  let _normal := pgroup_maximal_subgroup_normal prime prime_prime pgroup maximal coatom
  have quotient_card : Nat.card (GroupType ⧸ maximal) = prime := by
    rw [← Subgroup.index_eq_card]
    exact pgroup_maximal_subgroup_index prime prime_prime pgroup maximal coatom
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' maximal (element ^ prime) = 1
  rw [map_pow, ← quotient_card]
  exact pow_card_eq_one'

theorem pgroup_frattini_quotient_commutative (prime : ℕ) (prime_prime : prime.Prime)
    (pgroup : IsPGroup prime GroupType) : IsMulCommutative (GroupType ⧸ frattini GroupType) := by
  refine ⟨⟨?_⟩⟩
  intro first second
  obtain ⟨firstElement, rfl⟩ := QuotientGroup.mk'_surjective (frattini GroupType) first
  obtain ⟨secondElement, rfl⟩ := QuotientGroup.mk'_surjective (frattini GroupType) second
  apply commutatorElement_eq_one_iff_mul_comm.mp
  have member := pgroup_frattini_commutator_le prime prime_prime pgroup
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top firstElement) (Subgroup.mem_top secondElement))
  have identity : QuotientGroup.mk' (frattini GroupType) ⁅firstElement, secondElement⁆ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr member
  simpa only [commutatorElement_def, map_mul, map_inv] using identity

theorem pgroup_frattini_quotient_exponent (prime : ℕ) (prime_prime : prime.Prime)
    (pgroup : IsPGroup prime GroupType) (element : GroupType ⧸ frattini GroupType) : element ^ prime = 1 := by
  obtain ⟨representative, rfl⟩ := QuotientGroup.mk'_surjective (frattini GroupType) element
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (pgroup_frattini_power_mem prime prime_prime pgroup representative)

end CFSG.SignalizerFunctor.Helpers
