module

public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem elementary_abelian_hyperplane_generation (prime : ℕ) (prime_prime : prime.Prime)
    (actor target : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (actor_nontrivial : actor ≠ ⊥) (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card target)) :
    (⨆ hyperplane : Subgroup GroupType, ⨆ (_ : hyperplane ≤ actor),
      ⨆ (_ : (hyperplane.subgroupOf actor).index = prime),
        target ⊓ Subgroup.centralizer (hyperplane : Set GroupType)) = target := by
  let := elementary.1
  let _actorCommGroup : CommGroup actor := { actor.toGroup with mul_comm := mul_comm' }
  let : Fact prime.Prime := ⟨prime_prime⟩
  have actor_pgroup := elementary_abelian_isPGroup prime actor elementary
  obtain ⟨actorRank, actor_card⟩ := actor_pgroup.exists_card_eq
  have rank_positive : 0 < actorRank := by
    by_contra not_positive
    have rank_zero : actorRank = 0 := by omega
    rw [rank_zero, pow_zero] at actor_card
    exact actor_nontrivial ((Subgroup.eq_bot_iff_card actor).mpr actor_card)
  have rank_eq : actorRank = (actorRank - 1) + 1 := by omega
  have generation := elementary_abelian_centralizer_generation prime (actorRank - 1) prime_prime
    actor target elementary (by rw [← rank_eq]; exact actor_card.symm.le) normalized coprime
  apply le_antisymm
  · exact iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => inf_le_left
  · conv_lhs => rw [← generation]
    apply iSup_le
    intro hyperplane
    apply iSup_le
    intro member
    apply le_iSup_of_le hyperplane
    apply le_iSup_of_le member.1
    have index_eq : (hyperplane.subgroupOf actor).index = prime := by
      have cardinality := (hyperplane.subgroupOf actor).card_mul_index
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe member.1).toEquiv, member.2, actor_card,
        rank_eq, pow_succ] at cardinality
      exact Nat.eq_of_mul_eq_mul_left (pow_pos prime_prime.pos (actorRank - 1)) cardinality
    exact le_iSup_of_le index_eq le_rfl

end CFSG.SignalizerFunctor.Helpers
