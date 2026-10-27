module

public import CFSG.Monster.B.GSide.EdgeQCert
public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate16022
public import Certificates.Certificate3027
public import Certificates.Certificate16951

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open MulOpposite CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.CTIB

theorem psiS_mem_jOrbit_of_isConj
    {τ : Sbp} (hτ : τ ∈ Qs) (hc : IsConj labelS τ) :
    psiS τ ∈ jOrbit (qS 1) := by
  have hl1 : IsConj (rs 1) labelS := by
    rw [rs1_eq]
    exact (isConj_of_mem_jClass labelS_mem_jClass).symm
  have h1 : IsConj (rs 1) τ := hl1.trans hc
  have hsq : τ * τ = 1 := by
    obtain ⟨g, rfl⟩ := isConj_iff.1 hc
    have h := labelS_mem_jClass
    have hl : labelS * labelS = 1 := by
      obtain ⟨k, hk, e⟩ := h
      rw [e]
      calc k⁻¹ * qS 1 * k * (k⁻¹ * qS 1 * k) = k⁻¹ * (qS 1 * qS 1) * k := by group
        _ = 1 := by rw [sq_qS_one (.inl rfl)]; group
    calc g * labelS * g⁻¹ * (g * labelS * g⁻¹) = g * (labelS * labelS) * g⁻¹ := by group
      _ = 1 := by rw [hl]; group
  have hne : τ ≠ 1 := by
    rintro rfl
    obtain ⟨g, hg⟩ := isConj_iff.1 hc
    have : labelS = 1 := by
      calc labelS = g⁻¹ * (g * labelS * g⁻¹) * g := by group
        _ = 1 := by rw [hg]; group
    exact qS_ne_one (r := 1) (by decide) (by
      obtain ⟨k, hk, e⟩ := labelS_mem_jClass
      calc qS 1 = k * (k⁻¹ * qS 1 * k) * k⁻¹ := by group
        _ = 1 := by rw [← e, this]; group)
  have hmem : τ ∈ {t | t ∈ Qs ∧ t * t = 1 ∧ t ≠ 1} := ⟨hτ, hsq, hne⟩
  rw [invs_eq] at hmem
  rcases hmem with ((h | h) | h) | h
  · exact absurd (eq_of_conj_four (i := 1) (j := 0) (by simp) (by simp)
      (h1.trans (isConj_of_mem_jClass h))) (by norm_num)
  · rw [rs1_eq] at h
    obtain ⟨g, hg, rfl⟩ := h
    exact ⟨g, hg, rfl⟩
  · have h20 : IsConj (rs 2) (rs 0) := fusion_conj_at 0 (by norm_num)
    exact absurd (eq_of_conj_four (i := 1) (j := 0) (by simp) (by simp)
      ((h1.trans (isConj_of_mem_jClass h)).trans h20)) (by norm_num)
  · exact absurd (eq_of_conj_four (i := 1) (j := 3) (by simp) (by simp)
      (h1.trans (isConj_of_mem_jClass h))) (by norm_num)

theorem image_jOrbit_qS_one :
    wvEquiv hv0 '' jOrbit (qS 1) = Unitary.OmegaW := by
  have hl : psiS labelS ∈ jOrbit (qS 1) := by
    obtain ⟨g, hg, e⟩ := labelS_mem_jClass
    exact ⟨g, hg, by rw [e]⟩
  rw [← jOrbit_eq_of_mem (qS_mem 1) labelS_mem hl, jOrbit_eq_range labelS_mem,
    image_range_wvEquiv, wv_psiS_labelS, native_Co2_coset_fiber_data.2.2.2.2.1]
  rfl

@[expose] def ehatToS (t : Ehat) : Sbp := op ((ehatEquiv.symm t : Ebar) : Cbar)

theorem ehatToS_mem (t : Ehat) : ehatToS t ∈ Qs := (ehatEquiv.symm t).2

theorem iotaD_ehatToS (t : Ehat) : iotaD (ehatToS t).unop = t := by
  show iotaD ((ehatEquiv.symm t : Ebar) : Cbar) = t
  rw [← coe_ehatEquiv, MulEquiv.apply_symm_apply]

theorem psiW_eq_wvEquiv_psiS (t : Ehat) : psiW t = wvEquiv hv0 (psiS (ehatToS t)) := by
  rw [psiS_of_mem (ehatToS_mem t)]
  have e : (⟨(ehatToS t).unop, ehatToS_mem t⟩ : Ebar) = ehatEquiv.symm t := rfl
  rw [e, ← psiW_ehatEquiv, MulEquiv.apply_symm_apply]

theorem isConj_labelS_ehatToS {t : Ehat} {s : Shat} (hs : (t : Dfull) = (s : Dfull)⁻¹ * cQ * s) :
    IsConj labelS (ehatToS t) := by
  obtain ⟨σ₀, hσ⟩ := s.2
  rw [isConj_iff]
  refine ⟨op σ₀, ?_⟩
  apply unop_injective
  apply iotaD_injective
  rw [iotaD_ehatToS, hs, ← hσ]
  simp only [unop_mul, unop_inv, unop_op, map_mul, map_inv, iotaD_labelS]
  group

theorem psiW_mem_OmegaW_of_label
    {t : Ehat} {s : Shat}
    (hs : (t : Dfull) = (s : Dfull)⁻¹ * cQ * s) : psiW t ∈ Unitary.OmegaW := by
  rw [← image_jOrbit_qS_one, psiW_eq_wvEquiv_psiS]
  exact ⟨_, psiS_mem_jOrbit_of_isConj (ehatToS_mem t) (isConj_labelS_ehatToS hs), rfl⟩

theorem psiW_ne_zero_of_mem_OmegaW
    {t : Ehat} (h : psiW t ∈ Unitary.OmegaW) : psiW t ≠ 0 := by
  intro h0
  rw [native_Co2_coset_fiber_data.2.2.2.2.1] at h
  obtain ⟨k, hk⟩ := h
  have hk' : Short.wAct Co2.v0 k Unitary.sigmaW = psiW t := hk
  apply Unitary.sigmaW_ne_zero
  have e := Co2.wAct_inv_apply k Unitary.sigmaW
  rw [hk', h0, map_zero] at e
  exact e.symm

theorem exists_label_of_psiW_mem_OmegaW
    {t : Ehat} (h : psiW t ∈ Unitary.OmegaW) :
    ∃ s : Shat, (t : Dfull) = (s : Dfull)⁻¹ * cQ * s := by
  have h' := h
  rw [native_Co2_coset_fiber_data.2.2.2.2.1] at h'
  obtain ⟨k, hk⟩ := h'
  obtain ⟨j, rfl⟩ := jhatToKv0_surjective k
  set f : Ehat := ⟨(j : Dfull)⁻¹ * cQ * j, conj_mem_Ehat j.2 cQ_mem_Ehat⟩ with hf
  have hpf : psiW f = psiW t := by
    rw [hf, psiW_conj j.2 cQ_mem_Ehat, ← hk]
    congr 1
    exact psiW_cE
  have h0 : psiW (f⁻¹ * t) = 0 := by rw [psiW_mul, psiW_inv, hpf, neg_add_cancel]
  have hjS : (j : Dfull) ∈ Shat := Jhat_le_Shat j.2
  rcases (psiW_eq_zero_iff _).1 h0 with h1 | h1
  · refine ⟨⟨j, hjS⟩, ?_⟩
    have e : t = f := (inv_mul_eq_one.1 h1).symm
    rw [e]
  · have e : t = f * xhatE := inv_mul_eq_iff_eq_mul.1 h1
    obtain ⟨z, hz⟩ : ∃ z, bV (psiW t) z ≠ 0 := by
      by_contra hall
      push Not at hall
      exact psiW_ne_zero_of_mem_OmegaW h (bV_nondegenerate.1 _ hall)
    obtain ⟨y, rfl⟩ := psiW_surjective z
    have hb : bV (psiW f) (psiW y) = 1 := by
      rw [hpf]
      rcases Fischer.zmod2_cases (bV (psiW t) (psiW y)) with h2 | h2
      · exact absurd h2 hz
      · exact h2
    have hyS : (y : Dfull) ∈ Shat := Ehat_le_Shat y.2
    refine ⟨⟨j, hjS⟩ * ⟨y, hyS⟩, ?_⟩
    have hc := Ehat_comm f y
    rw [hb] at hc
    change ((f : Dfull)) * y = y * f * xhat ^ (1 : ZMod 2).val at hc
    rw [ZMod.val_one, pow_one] at hc
    rw [e]
    show (j : Dfull)⁻¹ * cQ * j * xhat = ((j : Dfull) * y)⁻¹ * cQ * ((j : Dfull) * y)
    have hf' : (f : Dfull) = (j : Dfull)⁻¹ * cQ * j := rfl
    calc (j : Dfull)⁻¹ * cQ * j * xhat = (y : Dfull)⁻¹ * (y * f * xhat) := by rw [hf']; group
      _ = (y : Dfull)⁻¹ * ((f : Dfull) * y) := by rw [hc]
      _ = ((j : Dfull) * y)⁻¹ * cQ * ((j : Dfull) * y) := by rw [hf']; group

theorem isLabel_iff_psiW_mem_OmegaW
    (t : Ehat) :
    (∃ s : Shat, (t : Dfull) = (s : Dfull)⁻¹ * cQ * s) ↔ psiW t ∈ Unitary.OmegaW :=
  ⟨fun ⟨_, hs⟩ => psiW_mem_OmegaW_of_label hs, exists_label_of_psiW_mem_OmegaW⟩

theorem exists_clabelS_iff
    (s : Shat) :
    (∃ v, s = clabelS v) ↔ ∃ g : Shat, (s : Dfull) = (g : Dfull)⁻¹ * cQ * g := by
  constructor
  · rintro ⟨v, rfl⟩
    have h : clabel v ∈ Set.range clabel := ⟨v, rfl⟩
    rw [CTIB.range_clabel] at h
    exact h
  · rintro ⟨g, hg⟩
    have h : (s : Dfull) ∈ Set.range clabel := by
      rw [CTIB.range_clabel]
      exact ⟨g, hg⟩
    obtain ⟨v, hv⟩ := h
    exact ⟨v, Subtype.ext (by rw [coe_clabelS, hv])⟩

end CFSG.Monster.B.GSide
