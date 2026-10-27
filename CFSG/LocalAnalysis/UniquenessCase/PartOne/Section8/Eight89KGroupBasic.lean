module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem card_eq_of_isAlt6_quot {K : Type} [Group K] (hA : IsAlt (K ⧸ center K) 6) :
    Nat.card K = 360 * Nat.card (center K) := by
  obtain ⟨eA⟩ := hA
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    rfl
  rw [Nat.card_congr eA.toEquiv, hA6] at h1
  exact h1

theorem normal_eq_top_or_le_center_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.IsQuasisimple Q) {N : Subgroup Q} (hN : N.Normal) :
    N = ⊤ ∨ N ≤ center Q := by
  have hp : commutator Q = ⊤ := Group.isPerfect_def.mp hQ.1
  have := hQ.2.1
  have := hN.map (QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (center Q))) with
    h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hcomm : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    exact eq_top_iff.mpr (hp ▸ hcomm)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
