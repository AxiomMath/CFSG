module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Dichotomy.Generic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Milestones.ASVolI.C61.PBasic245Single

public section

namespace CFSG.QuasithinUnique.burnsideC56_P

open CFSG.Open CFSG.Quasithin Subgroup

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem burnsideC56_a3Local (hcs : burnsideC56_CS G T M H S L) (h3 : IsAltType L 3)
    (hj : conjJoin S L = L) :
    ∃ c : G, A3Local H S L (blockU L) (H ⊓ Subgroup.centralizer (L : Set G)) c := by
  classical
  obtain ⟨hQU, hcardU, hUexp, hUcomm, hcardL, hZL, c, hcL, hc3, hcnorm, hfpf, hLeq⟩ :=
    hcs.block.1.1.alt3_structure h3
  have hH : H = L ⊔ S := by rw [hcs.eq_join, hj]
  have hSH : S ≤ H := hcs.sylow.1
  have hSL : S ≤ normalizer (L : Set G) := by
    have h1 : ∀ t ∈ S, L.map (MulAut.conj t).toMonoidHom ≤ L := by
      intro t ht
      have h : L.map (MulAut.conj t).toMonoidHom ≤ conjJoin S L :=
        le_iSup (fun s : S => L.map (MulAut.conj (s : G)).toMonoidHom) ⟨t, ht⟩
      rwa [hj] at h
    intro s hs
    apply A3Gen.mem_normalizer_of_map_conj_eq
    refine le_antisymm (h1 s hs) ?_
    intro x hx
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have h2 : (MulAut.conj s⁻¹) x ∈ L.map (MulAut.conj s⁻¹).toMonoidHom := ⟨x, hx, rfl⟩
    have h3 := h1 s⁻¹ (S.inv_mem hs) h2
    simpa [MulAut.conj_apply] using h3
  have hHL : H ≤ normalizer (L : Set G) := hH ▸ sup_le Subgroup.le_normalizer hSL
  have hHU : H ≤ normalizer (blockU L : Set G) := by
    intro h hh
    apply A3Gen.mem_normalizer_of_map_conj_eq
    rw [← hQU]
    unfold blockQ
    rw [← pCoreOf_map_equiv 2 (MulAut.conj h) L, A3Gen.map_conj_eq_of_mem_normalizer (hHL hh)]
  have hUL : blockU L ≤ L := hQU ▸ CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L
  obtain ⟨hUS, hcardH, hHD, hDS, hUD, hSC, hcardS⟩ :=
    A3Gen.a3_generic hH hSH hSL hcs.sylow.2.1
      (fun N hNH hHN hN2 => hcs.sylow.le_of_normalizes hNH hHN hN2) hHU hUL hcardU hUexp hUcomm
      hcL hcnorm hfpf hLeq hcardL hZL hcs.minParabolic.2.1
  exact ⟨c, hcardU, hUexp, hUcomm, hcL, hc3, hcnorm, hfpf, hLeq, hHL, hHU, hUS, hcardH, rfl, hDS,
    hHD, fun d hd l hl => (Subgroup.mem_centralizer_iff.mp hd.2 l hl).symm, hUD, hSC, hcardS⟩

theorem burnsideC56_a3Data (hcs : burnsideC56_CS G T M H S L) (hj : conjJoin S L = L) {c : G}
    (hl : A3Local H S L (blockU L) (H ⊓ Subgroup.centralizer (L : Set G)) c) {M₀ : Subgroup G}
    (hSM : S ≤ M₀) (hMT : M₀ ≤ T) (h2 : S.relIndex M₀ = 2) {x : G} (hx : x ∈ M₀)
    (hxS : x ∉ S) :
    A3Dich.Data S L (blockU L) (H ⊓ Subgroup.centralizer (L : Set G)) x := by
  have hH : H = L ⊔ S := C56.H_eq hcs hj
  have hLH : L ≤ H := hH ▸ le_sup_left
  have hSH : S ≤ H := hcs.sylow.1
  exact
    { card_U := hl.card_U
      U_comm := hl.U_comm
      U_le := hl.U_le_S
      D_le := hl.D_le_S
      U_inf_D := hl.U_inf_D
      S_cent_U := hl.S_cent_U
      card_S := hl.card_S
      S_norm_U := hSH.trans hl.H_normalizes_U
      S_norm_D := hSH.trans hl.H_normalizes_D
      L_norm_U := hLH.trans hl.H_normalizes_U
      D_comm_L := hl.D_comm_L
      x_norm := normalizer_of_relIndex_two hSM h2 hx
      x_sq := by rw [pow_two]; exact mul_self_mem_of_relIndex_two h2 hx hxS
      h244 := fun S₀ hS₀ hS₀S hSN hLN hxN => by
        have e := hcs.l244 S₀ hS₀ hS₀S (hH ▸ sup_le hLN hSN)
        have : x ∈ T ⊓ normalizer (S₀ : Set G) := ⟨hMT hx, hxN⟩
        rw [e] at this
        exact hxS this }

end CFSG.QuasithinUnique.burnsideC56_P
