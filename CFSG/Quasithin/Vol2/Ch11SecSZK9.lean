module

public import CFSG.Quasithin.Vol2.Ch11SecSZK8
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecSSym5
public import CFSG.Quasithin.Vol2.Ch11SecSZK
public import CFSG.Quasithin.Vol2.Ch11SecSZK3
public import CFSG.Quasithin.Vol2.Ch11SecSZK4
public import CFSG.Quasithin.Vol2.Ch11SecSZK7

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G}

theorem typeData_of_le
    (hF02 : Facts02) (hNot : FactL34NotL42) (h312 : A312ForSQTK)
    (h : StarHyp G T L I V₁ V₂ X K) {Kp : Subgroup G} (hKKp : K ≤ Kp)
    (hKpl : quasithinIsLocal T Kp) : TypeData (↥Kp ⧸ CFSG.pCore 2 ↥Kp) := by
  have hS := isSylowTwoOf_of_quasithinIsSylowTwo h.sylow (le_sup_right : T ≤ Kp ⊔ T)
  have hKH : K ≤ Kp ⊔ T := hKKp.trans le_sup_left
  have hI : Kp ∈ cComp (Kp ⊔ T) := cComp_of_isLocal hKpl
  obtain ⟨e₁⟩ := modO2Image_quotEquiv hKH
  have hD := l34Data_of (isPSL_of_mulEquiv e₁.symm h.psl)
  obtain ⟨e₂⟩ := modO2_mulEquiv hI
  rcases CFSG.Quasithin.lemma_1_2_4_list h.hyp.fsu.qtke h.hyp.fsu.simple h.hyp.fsu.nonabelian
      h312 hKpl.2.2.2 hS hKH (mem_lFamily_of_isLocal h.isLocal_K) hI hKKp with heq | hc | hnq
  · obtain rfl : K = Kp := eq_of_modO2Image_eq hS (le_of_mem_cComp hI) hKKp
      (perfect_of_mem_cComp hI) h.T_le_normalizer_K heq
    exact typeData_of_isPSL hF02.l34 h.psl
  · exact (typeData_of_M23 (hD.of_a312Case hNot hc)).of_mulEquiv e₂.symm
  · exact (hD.false_of_nonquasi (Subgroup.map_mono fun x hx => hKKp hx) hnq).elim

end StarHyp

theorem obl11_1_2StarZK_of
    (hNot : FactL34NotL42) (hF02 : Facts02) (h128 : Lemma128One)
    (h37 : A37ForSQTK) (h312 : A312ForSQTK) (hfsu : Ch10.StmtFSUChoice) (h701 : Stmt7_0_1)
    (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) (h8 : Ch10.TmpL6_3_2_2_eight)
    (hM24 : IsSimpleGroup ↥NativeSporadic.M24)
    (hM24c : Nat.card ↥NativeSporadic.M24 = 2 ^ 10 * 239085) : Obl11_1_2StarZK := by
  intro G _ _ T L I V₁ V₂ X K h
  by_contra hZK
  have hQ := h.hyp.fsu.qtke
  have hs := h.hyp.fsu.simple
  have hnab := h.hyp.fsu.nonabelian
  have hKl := h.isLocal_K
  obtain ⟨Kp, hKKp, hmax, hf⟩ := exists_maximalFaithful_ge hQ hs hnab h37 h128 h.sylow
    (isFaithfulLocal_of_omegaOneCenter hQ h.sylow hKl hZK)
  have hTKp : T ≤ Subgroup.normalizer (Kp : Set G) := fun t ht =>
    (lemma_1_2_8_one_le hQ hs hnab h37 hKl hf.1 hKKp ⟨ht, h.T_le_normalizer_K ht⟩).2
  have hD := h.typeData_of_le hF02 hNot h312 hKKp hf.1
  obtain ⟨Ip, hfsu'⟩ := hfsu G T Kp hs hnab hQ h.sylow hmax hf hD.isQuasisimple
  obtain ⟨e⟩ := nonempty_quot_mulEquiv_autOn h8 hfsu' hTKp hD.simple
  have hD' := hD.of_mulEquiv e
  obtain ⟨hcomm, -, -, hcases⟩ := h701 G T Kp Ip hfsu'
  rcases hcases with hFF | hJ | hO | hF
  · rcases concl701FF_list h325 h328 hfsu' hTKp hFF with hl | ⟨-, ht⟩
    · exact hD'.not_list325 hl
    · exact hD'.not_type328 hF02 hTKp ht
  · exact hD'.not_concl701J4 hM24 hM24c hTKp hJ
  · exact hD'.not_concl701Orth hTKp hO
  · exact not_concl701Four_of_le_normalizer hTKp hF

end CFSG.Quasithin.Vol2.Ch11.SecS
