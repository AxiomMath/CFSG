module

public import CFSG.Milestones.ASVolI.C61.PAppDD9

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppD

open CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open CFSG.QuasithinUnique.burnsideC56_P.AppC
open CFSG.QuasithinUnique.AppC hiding Cfg Cfg.D_le_Q Cfg.Q_comm_U Cfg.Q_eq Cfg.S_le_N_D
  Cfg.UD_unique Cfg.U_comm_D Cfg.U_inf_D Cfg.aU_spec Cfg.blockU_le_baum Cfg.card_Q Cfg.card_U
  Cfg.conj_mem_blockD Cfg.exists_UD Cfg.hL Cfg.hQ Cfg.hQS Cfg.hSH Cfg.hSN Cfg.hU Cfg.hUQ Cfg.hUS
  Cfg.im_le_Dstd Cfg.mem_Q_iff Cfg.mem_Q_of_pf_eq_one Cfg.omegaOneCenter_le_pCoreOf
  Cfg.pf_eq_one_of_mem_Q Mate.B_eq Mate.B_eq_sup Mate.B_le_sup Mate.D_comm_V Mate.D_elem
  Mate.D_inf_conj Mate.D_le_B Mate.D_le_K Mate.D_le_of_isMax Mate.G_spec Mate.J_eq_B Mate.Q_elem
  Mate.Q_isMax Mate.Q_le_B Mate.Qx_isMax Mate.S_le_N_V Mate.V_comm Mate.V_conj Mate.V_elem
  Mate.V_inf_Q_le_U Mate.V_le_B Mate.V_le_S Mate.V_not_le_Q Mate.V_sq Mate.X'_spec Mate.Yv_isMax
  Mate.Yv_le Mate.baumD_eq Mate.card_V Mate.card_eq_Q Mate.card_symm Mate.cent_U_V Mate.conj_K
  Mate.eq_Q_of_type_bot Mate.eq_Yv_of_type_t1 Mate.exists_vud Mate.fixU_le_of_isMax Mate.fix_mem
  Mate.im_V Mate.pf_ne_one Mate.sqSub_D Mate.sqSub_K Mate.type_cases a5_core a5_core_std
  blockD_le_pCoreOf blockQ_comm_pCoreOf blockU_inf_blockD card_im_S exists_mem_thompsonJ_pi_ne_one
  exists_split exists_split' nonempty_cfg pCoreOf_comm_blockU pCoreOf_eq_blockU_sup_blockD
  swapGen_imJ

variable {G : Type} [Group G] [Finite G]

theorem c61_gen {T M H S L : Subgroup G} (C : GCfg T M H S L)
    (hO2 : blockU0 S L = pCoreOf 2 (conjJoin S L))
    (hvac : conjJoin S L = L → ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3) → False)
    (hcase : (IsAltType L 5 ∧ conjJoin S L = L) ∨ (IsAltType L 3 ∧ conjJoin S L ≠ L))
    (hA3 : IsAltType L 3 → conjJoin S L = L → False) : C61Concl T H S L := by
  obtain ⟨M₀, hSM, hMT, h2⟩ := C56.exists_index_two C.hcs
  have hne : S ≠ M₀ := fun h => by
    rw [← h] at h2
    simp at h2
  obtain ⟨x₀, hx₀, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hSM hcon)
  have m₀ : GMate S T M₀ x₀ := ⟨hSM, hMT, h2, hx₀, hx₀S⟩
  have hNT : normT T S = M₀ := GMate.normT_eq (m := m₀) C
  have hJ : thompsonJ M₀ = thompsonJ S := thompsonJ_M₀_eq C hSM hMT h2
  have hbaum : ∀ x ∈ M₀, x ∉ S → baum S = pCoreOf 2 H ⊔ conjR (pCoreOf 2 H) x := by
    intro x hx hxS
    have m : GMate S T M₀ x := ⟨hSM, hMT, h2, hx, hxS⟩
    refine C56.baum_eq_sup_conj (L := L) (normalizer_of_relIndex_two hSM h2 hx) ?_ ?_
    · rw [GMate.baumD_eq (m := m) C, ← C.hUdef, C.hQeq, sup_comm]
    · rw [GMate.baumD_eq (m := m) C, ← C.hUdef]
      exact GMate.B_eq (m := m) C
  refine ⟨⟨by rw [hNT]; exact h2, fun x hxN hxS => ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hNT] at hxN
    have m : GMate S T M₀ x := ⟨hSM, hMT, h2, hxN, hxS⟩
    exact ⟨GMate.J_eq_B (m := m) C, hbaum x hxN hxS⟩
  · intro hj hor
    exact (hvac hj hor).elim
  · intro _ x hxN hxS r hrS hrJ
    rw [hNT] at hxN
    have m : GMate S T M₀ x := ⟨hSM, hMT, h2, hxN, hxS⟩
    exact GMate.a5_classification (m := m) C hrS (by rw [← GMate.J_eq_B (m := m) C]; exact hrJ)
  · rw [C.hQeq, C.hUdef, hO2, sup_comm]
  · by_cases hTM : M₀ = T
    · left
      refine ⟨?_, ?_, fun h3 hj => (hA3 h3 hj).elim⟩
      · rw [← hTM]; exact h2
      · rw [← hTM]; exact hJ.symm
    · right; right
      obtain ⟨F⟩ := GMate.nonempty_four (m := m₀) C
      refine ⟨hcase, ?_, ?_, ?_⟩
      · rw [hNT]; exact hJ.symm
      · rw [hNT, GMate.J_eq_B (m := m₀) C]
        exact GMate.rho_dihedral (m := m₀) C F C.hcs.T_two hTM
      · intro A₁ hA₁ hAQ _
        obtain ⟨i, rfl⟩ := (GMate.members (m := m₀) C F).1 hA₁
        have hi : i ≠ 0 := fun h => hAQ (by rw [h]; rfl)
        exact GMate.card_normalizer_pair (m := m₀) C F C.hcs.T_two hTM hi

end CFSG.QuasithinUnique.burnsideC56_P.AppD
