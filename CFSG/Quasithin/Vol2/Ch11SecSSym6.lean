module

public import CFSG.Quasithin.Vol2.Ch11SecSSym5
public import CFSG.Quasithin.Vol2.Ch11SecSCartan
public import CFSG.Quasithin.Vol2.Ch11SecSSym2
public import CFSG.Quasithin.Vol2.Ch11SecSSym4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

theorem obl11_1_2StarSym_of (hF : FactL34Parab) (hLevi : FactL34Levi) (hT : FactPGL34Torus)
    (hNo : FactL34NoE9) (hPG : FactParabGen) (hC : CartanFacts) (hN : NatFacts)
    (hG2 : FactG2DerivedOrder) (hG2a : FactG2AdjointOrder) (hRQ : RankTwoQuasisimple)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h128 : Lemma128Four)
    (hfsu : Ch10.StmtFSUChoice) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hZL : Obl11_1_2StarZL2) (hZK : Obl11_1_2StarZK) (hRole : Obl11_1_2StarSymRole) :
    Obl11_1_2StarSym := by
  intro G _ _ T L I V₁ V₂ X K K₀ h hK0 hnSL hY hI₀ hTI₀ hXI₀ hshape
  have hK0' := hK0
  obtain ⟨hK₀, hK₀K, hne, hne₁⟩ := hK0
  have hL₁ne : LOf L V₁ ≠ ⊥ :=
    ne_bot_of_mem_cComp (lOf_mem_lFamily hN h1102 h.hyp h.v₁ (Or.inl rfl) le_rfl)
  obtain ⟨P₁, P₂, hP⟩ := h.exists_parData hF hL₁ne
  obtain ⟨cL, -, -⟩ := cartan_of hC hN hG2 h1102 h.hyp h.v₁ h.v₂ h.cartan
  have hK₀eq : K₀ = k0Of K P₂ := by
    rcases h.eq_of_isLocal_le hP hK₀ hK₀K with h1 | h1 | h1
    · exact absurd h1 hne
    · exact absurd h1 hne₁
    · exact h1
  subst hK₀eq
  have hn := h.not_isPSL_of_le hNo hLevi hT hN h1102 cL hP hTI₀ le_sup_left le_sup_right hXI₀
  have hloc := h.isLocal_of_mem_cComp_Y le_sup_right hY hI₀
  have hmax := h.isMaximalLocal_of_shape h128 hG2a hloc hshape hn
  have hf := h.isFaithfulLocal_J hZL le_sup_right hY hI₀ le_sup_right
  obtain ⟨I', hJ⟩ := h.exists_hyp11_J hfsu hRQ hmax hf hTI₀ hshape
  obtain ⟨hex, -, -⟩ := h1110 G T _ I' 2 hJ
  obtain ⟨U₁, hU₁, -⟩ := hex 1 le_rfl (by norm_num)
  obtain ⟨U₂, hU₂, -⟩ := hex 2 (by norm_num) (by norm_num)
  have hZK' := hZK G T L I V₁ V₂ X K h
  have hCV := h.fsuV_inf_centralizer_eq_bot hPG h37 h38 h39 hN h1102 cL hJ hloc le_sup_right hZK'
  obtain ⟨hU₁eq, hU₂eq, hcart, hKU, hKc⟩ := hRole G T L I V₁ V₂ X K _ I' U₁ U₂ h hK0' hnSL hY
    hI₀ hTI₀ hXI₀ hshape hn hJ hU₁ hU₂ hZK' hCV
  have hKn := h.normalizer_le_of_cComp h37 h38 (IsVi.ne_bot hJ hU₁ le_rfl)
    ((isPGroup_fsuV hJ).to_le (IsVi.le_fsuV hU₁)) hU₁.2 (h.isLocal_k0Of hP) (k0Of_le K P₂)
    (h.T_le_normalizer_k0Of hP) hKc
  refine ⟨I', U₁, U₂, ⟨hJ, hU₁, hU₂, hcart, hKc, hKn, ?_, ?_, h.charTwo, hKU, h.psl, ?_⟩,
    hU₁eq, hU₂eq⟩
  · rw [hU₁eq]
    exact lt_of_le_of_ne (k0Of_le K P₂) (StarHyp.k0Of_ne_K hP)
  · exact h.not_le_normalizer_of_isLocal hPG h37 h38 h39 hN h1102 cL hloc hTI₀ le_sup_right
  · rw [hU₁eq]
    exact h.pgl_k0Of hLevi hT hN h1102 cL hP

end CFSG.Quasithin.Vol2.Ch11.SecS
