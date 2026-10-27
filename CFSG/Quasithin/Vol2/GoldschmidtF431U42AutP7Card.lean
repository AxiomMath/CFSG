module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Cls
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Mod1

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_x)

@[expose] def gensP2 : Set Ah := Set.range (fun k : Fin 5 => gTA k) ∪ {fhatA, c3A, bA}

theorem gTA_mem_Bh (k : Fin 5) : gTA k ∈ Bh := by
  have := U42.gTY_mem_B0 k k.2
  rw [← comap_Bh] at this
  exact this

theorem closure_gensP1 :
    Subgroup.closure gensP1 = P1h := by
  refine le_antisymm ?_ P1h_le_closure
  rw [Subgroup.closure_le]
  intro g hg
  rw [gensP1] at hg
  rcases hg with ⟨k, rfl⟩ | rfl | rfl | rfl
  · exact Bh_le_P1h (gTA_mem_Bh k)
  · exact fhatA_mem_P1h
  · exact Bh_le_P1h c3A_mem_Bh'
  · exact D1A_mem_P1h

theorem closure_gensP2 :
    Subgroup.closure gensP2 = P2h := by
  have hle : Subgroup.closure gensP2 ≤ P2h := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [gensP2] at hg
    rcases hg with ⟨k, rfl⟩ | rfl | rfl | rfl
    · exact Bh_le_P2h (gTA_mem_Bh k)
    · exact fhatA_mem_P2h
    · exact Bh_le_P2h c3A_mem_Bh'
    · exact bA_mem_P2h
  refine le_antisymm hle ?_
  set K := Subgroup.closure gensP2 with hK
  have hBK : Bh ≤ K := Bh_le_closure.trans (Subgroup.closure_mono (by
    intro g hg
    rcases hg with hg | rfl | rfl
    · exact Or.inl hg
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))))
  have hbK : bA ∈ K := Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl)))
  rcases lattice_Bh (H := K ⊓ P2h) (le_inf hBK Bh_le_P2h) with h | h | h | h
  · exfalso
    have : bA ∈ K ⊓ P2h := ⟨hbK, bA_mem_P2h⟩
    rw [h] at this
    exact bA_not_mem_P1h this.1
  · exfalso
    exact P1h_not_le_P2h (h ▸ inf_le_right)
  · exact h ▸ inf_le_left
  · exfalso
    have h1 : (⊤ : Subgroup Ah) ≤ P2h := h ▸ inf_le_right
    have := Subgroup.card_le_of_le h1
    rw [Subgroup.card_top, card_A, card_P2h] at this
    omega

theorem card_C1 :
    Nat.card ↥(P1h ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) = 96 := by
  rw [card_inf_centralizer fhatA_mem_P1h]
  have hgl : ∀ s ∈ gensP1, ∃ sL ∈ genP1L, RepL sL (s : P45) := by
    intro s hs
    rw [gensP1] at hs
    rcases hs with ⟨k, rfl⟩ | rfl | rfl | rfl
    · exact ⟨gTL k, List.mem_append.2 (Or.inl (List.mem_map.2 ⟨k, List.mem_range.2 k.2, rfl⟩)),
        repL_gTA k⟩
    · exact ⟨fhatL, by simp [genP1L], repL_fhat⟩
    · exact ⟨c3L, by simp [genP1L], U42.repL_c3⟩
    · exact ⟨DL 1, by simp [genP1L], U42.repL_Dj 1⟩
  have h := card_cent_fhat_of_class closure_gensP1 fhatA_mem_P1h cls1w genP1L hgl
    (fun w hw => mem_P1h_of_repL (repL_aW w) (cls1_mem w hw)) cls1_check.1 cls1_check.2.1
    cls1_check.2.2
  have hl : cls1w.length = 12 := by decide +kernel
  rw [hl, card_P1h] at h
  omega

theorem card_C2 :
    Nat.card ↥(P2h ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) = 96 := by
  rw [card_inf_centralizer fhatA_mem_P2h]
  have hgl : ∀ s ∈ gensP2, ∃ sL ∈ genP2L, RepL sL (s : P45) := by
    intro s hs
    rw [gensP2] at hs
    rcases hs with ⟨k, rfl⟩ | rfl | rfl | rfl
    · exact ⟨gTL k, List.mem_append.2 (Or.inl (List.mem_map.2 ⟨k, List.mem_range.2 k.2, rfl⟩)),
        repL_gTA k⟩
    · exact ⟨fhatL, by simp [genP2L], repL_fhat⟩
    · exact ⟨c3L, by simp [genP2L], U42.repL_c3⟩
    · exact ⟨evalAL wb, by simp [genP2L], repL_bA⟩
  have h := card_cent_fhat_of_class closure_gensP2 fhatA_mem_P2h cls2w genP2L hgl
    (fun w hw => mem_P2h_of_repL (repL_aW w) (cls2_mem w hw)) cls2_check.1 cls2_check.2.1
    cls2_check.2.2
  have hl : cls2w.length = 20 := by decide +kernel
  rw [hl, card_P2h] at h
  omega

end CFSG.Quasithin.H13.F431.U42Aut
