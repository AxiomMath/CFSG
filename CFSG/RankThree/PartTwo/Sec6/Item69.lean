module

public import CFSG.RankThree.PartTwo.Sec6.Item612

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_normalizer_of_commutator_le {L X : Subgroup G} (h : ⁅L, X⁆ ≤ L) :
    X ≤ Subgroup.normalizer (L : Set G) := by
  refine le_normalizer_of_forall_conj_mem fun t ht x hx => ?_
  have h1 : ⁅x⁻¹, t⁆ ∈ L := h (Subgroup.commutator_mem_commutator (inv_mem hx) ht)
  rw [commutatorElement_def, inv_inv] at h1
  have h2 := L.mul_mem hx h1
  rwa [show x * (x⁻¹ * t * x * t⁻¹) = t * x * t⁻¹ by group] at h2

theorem rank3II_6_9 (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9) : Item6_9 := by
  intro G _ _ hG A hA E hE T hT B hBE hBab hB9
  have hTE : E ≤ Subgroup.centralizer (T : Set G) := (mem_fourGroupsPlus_iff.mp hT).2
  obtain ⟨hT2, hT1⟩ := isPGroup_two_and_ne_bot_of_mem_fourGroups hT.1
  have hB1 : B ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hB9
    norm_num at hB9
  obtain ⟨b, hbB, hb1, hV⟩ := exists_commutator_inf_centralizer_ne_bot hG.charTwoType hT2 hT1
    hBab hB9.ge (hBE.trans hTE) le_rfl hB1
  have hbE := hBE hbB
  obtain ⟨L, hL, hVL, hLV⟩ := exists_mem_thetaComponentsAt_moved hG h45 hA hE hT.1 hBE
    (hBE.trans hTE) hbE (hTE hbE) hb1 hV
  obtain ⟨hV2, hVS, hEV, hVF⟩ := commutator_inf_props hE hT.1 hBE hbE
  obtain ⟨-, hEL, hLE, hL0, -⟩ := props_of_moved hG h45 h49 hA hE hbE hb1 hL hV2
    (hVS.trans inf_le_right) hEV (hVF.le.trans (Subgroup.commutator_mono le_rfl hBE)) hVL hLV
  refine ⟨b, hbB, hb1, L, ⟨lZero_subset_lZeroUnion hE.1 hE.2 hL0, hL⟩, fun hLT => ?_⟩
  have hTL := le_normalizer_of_commutator_le (hLT.trans (theta_le L))
  have hLT' := commutator_eq_of_mem_fourGroups hA hE hT.1 hbE hb1 (hTE hbE) hL hEL hLE hTL hVS
    hVL hLV
  rw [hLT'] at hLT
  exact theta_ne_of_mem_thetaComponentsAt hL (le_antisymm (theta_le L) hLT)

end CFSG.RankThree.PartTwo.Sec6
