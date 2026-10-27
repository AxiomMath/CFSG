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
  letI : IsCyclic S := by
    simpa using hcyc
  rcases S.normalizer_le_centralizer_or_le_commutator with hNC | hScomm
  · left
    have hnot_card_comm : ¬ p ∣ Nat.card (commutator G) := by
      intro hp_dvd_comm
      have hcard_dvd_index : Nat.card (commutator G) ∣ (S : Subgroup G).index := by
        rw [(MonoidHom.ker_transferSylow_isComplement' S hNC).index_eq_card]
        exact Subgroup.card_dvd_of_le (Abelianization.commutator_subset_ker _)
      exact S.not_dvd_index (hp_dvd_comm.trans hcard_dvd_index)
    have hInfP : IsPGroup p ↥((S : Subgroup G) ⊓ commutator G) := S.isPGroup'.to_inf_left
    rcases hInfP.card_eq_or_dvd with hInfCard | hInfDvd
    · exact Subgroup.card_eq_one.mp hInfCard
    · exfalso
      exact hnot_card_comm (hInfDvd.trans (Subgroup.card_dvd_of_le inf_le_right))
  · right
    exact hScomm
