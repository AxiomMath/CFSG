module

public import Mathlib.GroupTheory.SpecificGroups.ZGroup

namespace CFSG
end CFSG
open CFSG

open scoped IsMulCommutative

/-!
# Cyclic Sylow intersection with commutator
-/

/-- If a Sylow subgroup is cyclic, then its intersection with the commutator subgroup is either
trivial or the Sylow subgroup lies in the commutator subgroup. -/
public theorem CFSG.sylow_inf_commutator_eq_bot_or_le_commutator
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (S : Sylow p G)
    (hcyc : IsCyclic (↥(S : Subgroup G))) :
    ((S : Subgroup G) ⊓ commutator G = ⊥) ∨ (S : Subgroup G) ≤ commutator G := by
  let : IsCyclic S := by
    simpa using hcyc
  rcases Sylow.not_dvd_card_commutator_or_not_dvd_index_commutator S with hnot_card | hnot_index
  · left
    have hInfP : IsPGroup p ↥((S : Subgroup G) ⊓ commutator G) := S.isPGroup.to_inf_left
    rcases hInfP.card_eq_or_dvd with hInfCard | hInfDvd
    · exact Subgroup.card_eq_one.mp hInfCard
    · exfalso
      exact hnot_card (hInfDvd.trans (Subgroup.card_dvd_of_le inf_le_right))
  · right
    have hpg : IsPGroup p ↥(Subgroup.map (QuotientGroup.mk' (commutator G)) (S : Subgroup G)) :=
      IsPGroup.map S.isPGroup _
    have hdvd : Nat.card ↥(Subgroup.map (QuotientGroup.mk' (commutator G)) (S : Subgroup G))
        ∣ (commutator G).index := by
      rw [Subgroup.index_eq_card, ← Subgroup.card_top (G := G ⧸ commutator G)]
      exact Subgroup.card_dvd_of_le le_top
    have hbot : Subgroup.map (QuotientGroup.mk' (commutator G)) (S : Subgroup G) = ⊥ :=
      Subgroup.card_eq_one.mp <|
        (hpg.card_eq_or_dvd.resolve_right fun h => hnot_index (h.trans hdvd))
    have hle := (Subgroup.map_eq_bot_iff (f := QuotientGroup.mk' (commutator G))
      (S : Subgroup G)).mp hbot
    rwa [QuotientGroup.ker_mk'] at hle
