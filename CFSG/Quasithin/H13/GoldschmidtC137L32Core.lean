module

public import CFSG.Quasithin.H13.U3L14Blk

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Quasithin.H13.U3

variable {G : Type} [Group G]

theorem charNormal_of_baum_eq [Finite G] {X R Q : Subgroup G}
    (hXQ : X ≤ normalizer (Q : Set G)) (hE : ∃ E ≤ Q, IsElemAbelian 2 E ∧ E ≠ ⊥)
    (h : baum R = baum Q) : CharNormal (baum R) X := by
  refine ⟨baum R, le_rfl, ?_, ?_, ?_⟩
  · obtain ⟨E, hEQ, hE2, hE0⟩ := hE
    obtain ⟨A, hA⟩ := exists_isMaxElemAbelian Q
    have hE1 : 1 < Nat.card E := (Subgroup.one_lt_card_iff_ne_bot _).2 hE0
    have hAE : Nat.card E ≤ Nat.card A := hA.2.2 E hEQ hE2
    have hA0 : A ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hAE
      omega
    intro hb
    apply hA0
    rw [h] at hb
    exact le_bot_iff.1 (hb ▸ (le_iSup₂_of_le A hA le_rfl).trans (B2F.thompsonJ_le_baum Q))
  · rw [Subgroup.subgroupOf_self]
    infer_instance
  · rw [h]
    exact hXQ.trans (normalizer_le_normalizer_baum Q)

end CFSG.Quasithin.H13.U3.GC137
