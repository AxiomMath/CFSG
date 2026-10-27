
module

public import CFSG.Monster.B.TwoA.Amalgam.CoFiberGraphAdjBase

public import CFSG.Monster.B.TwoA.Amalgam.CoFiberGraphPi

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Co2 (v0 wAct_mul wAct_one wAct_inv_apply wAct_apply_inv decW)

theorem not_adj_cv0_of_tauOrb
    {k : Jhat}
    (hk : (piPt k : Wv v0) ∈ Unitary.usigOrbit Unitary.tauW) :
    ¬ cgraph.Adj cv0 (cvOf (jhatS k)) := by
  intro h
  have hc := (clabel_adj h).2.1
  rw [clabel_cv0, clabel_jhatS] at hc
  have hb : bV (psiW cE) (psiW (labE k)) = 1 := by
    rw [psiW_cE, ← piPt_eq_psiW]
    exact bV_sigmaW_of_mem_tauOrb hk
  have he := Ehat_comm cE (labE k)
  rw [hb, ZMod.val_one, pow_one] at he
  have he' : cQ * (labE k : Dfull) = labE k * cQ * xhat := he
  exact xhat_ne_one (mul_eq_left.1 (he'.symm.trans hc))

theorem exists_H1_not_mem_Usig :
    ∃ h : Jhat, (h : Dfull) ∈ H1 ∧ jhatToKv0 h ∉ Unitary.Usig := by
  by_contra hc
  push Not at hc
  have hle : Co2Inv.Cr ≤ Unitary.Usig := by
    intro g hg
    obtain ⟨h, rfl⟩ := jhatToKv0_surjective g
    exact hc h ((mem_H1_iff h).2 ⟨h.2, hg⟩)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Co2Inv.natCard_Cr, Unitary.natCard_Usig] at hdvd
  norm_num at hdvd

theorem exists_adj_cv0_ne_sigma :
    ∃ h : Jhat, cgraph.Adj cv0 (cvOf (jhatS h)) ∧ (piPt h : Wv v0) ≠ Unitary.sigmaW := by
  obtain ⟨h, hH, hU⟩ := exists_H1_not_mem_Usig
  have hne : cvOf (jhatS h) ≠ cv0 := by
    intro e
    apply hU
    have hE : (h : Dfull) ∈ Eam := (cvOf_eq_cv0_iff _).1 e
    exact jhatToKv0_mem_Usig (Eam_inf_Jhat_le ⟨hE, h.2⟩)
  refine ⟨h, cSigma_isClique (mem_cSigma_one.2 ⟨1, Xgrp.one_mem, rfl⟩)
    (mem_cSigma_one.2 ⟨jhatS h, H1_le_Xgrp hH, rfl⟩) hne.symm, fun e => hU ?_⟩
  exact Unitary.mem_Usig.2 e

theorem adj_cv0_of_delta
    {k : Jhat} (hk : (piPt k : Wv v0) ∈ Unitary.DeltaW) :
    cgraph.Adj cv0 (cvOf (jhatS k)) := by
  obtain ⟨h, hadj, hσ⟩ := exists_adj_cv0_ne_sigma
  have hΔ : Unitary.usigOrbit (piPt h) = Unitary.DeltaW := by
    rcases Unitary.usigOrbit_of_mem_OmegaW (piPt h).2 with e | e | e
    · have h1 := Unitary.mem_usigOrbit_self (piPt h : Wv v0)
      rw [e] at h1
      exact absurd h1 hσ
    · exact e
    · have h1 := Unitary.mem_usigOrbit_self (piPt h : Wv v0)
      rw [e] at h1
      exact absurd hadj (not_adj_cv0_of_tauOrb h1)
  have hmem : cvOf (jhatS k) ∈ p1Orb (cvOf (jhatS h)) := by
    rw [p1Orb_eq hσ]
    exact ⟨k, rfl, hΔ ▸ hk⟩
  obtain ⟨p, hp, hpk⟩ := hmem
  rw [hpk, ← (cvMul_cv0_iff p).2 (Pc_le_Eam 0 hp), cgraph_adj_cvMul]
  exact hadj

theorem adj_cv0_iff_piPt
    {k : Jhat} (hk : cvOf (jhatS k) ≠ cv0) :
    cgraph.Adj cv0 (cvOf (jhatS k)) ↔
      (piPt k : Wv v0) = Unitary.sigmaW ∨ (piPt k : Wv v0) ∈ Unitary.DeltaW := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨hσ, hΔ⟩ := hc
    have hΩ := (Set.ext_iff.1 Unitary.OmegaW_eq_union _).1 (piPt k).2
    rcases hΩ with (h1 | h1) | h1
    · exact hσ h1
    · exact hΔ h1
    · exact not_adj_cv0_of_tauOrb h1 h
  · rintro (h | h)
    · have h1 : piPt 1 = piPt k := Subtype.ext (coe_piPt_one.trans h.symm)
      rcases piPt_eq_iff.1 h1 with h2 | h2
      · exact absurd h2 hk
      · rw [h2, mul_one, cvOf_jhatS_a0J]
        exact adj_cv0_elS a0_mem_Ehat a0_not_mem_N1
    · exact adj_cv0_of_delta h

theorem adj_jhatS_iff
    {k k' : Jhat} (hne : cvOf (jhatS k) ≠ cvOf (jhatS k')) :
    cgraph.Adj (cvOf (jhatS k)) (cvOf (jhatS k')) ↔
      piPt k = piPt k' ∨ Unitary.omegaGraph.Adj (piPt k) (piPt k') := by
  set m := k' * k⁻¹ with hm
  have hk' : k' = m * k := by rw [hm, inv_mul_cancel_right]
  have e0 : cvMul (cvOf (jhatS k)) (jhatS k⁻¹) = cv0 := by
    rw [cvMul_jhatS, mul_inv_cancel, cvOf_jhatS_one]
  have e1 : cvMul (cvOf (jhatS k')) (jhatS k⁻¹) = cvOf (jhatS m) := cvMul_jhatS _ _
  have hm0 : cvOf (jhatS m) ≠ cv0 := by
    rw [← e0, ← e1]
    intro h
    exact hne (cvMul_injective _ h).symm
  rw [← cgraph_adj_cvMul _ _ (jhatS k⁻¹), e0, e1, adj_cv0_iff_piPt hm0]
  have hpk' : (piPt k' : Wv v0) = wAct v0 (jhatToKv0 k) (piPt m) := by rw [hk', coe_piPt_mul]
  have hpk : (piPt k : Wv v0) = wAct v0 (jhatToKv0 k) Unitary.sigmaW := coe_piPt k
  have hsmul : ∀ x : Unitary.OmegaPt, (((jhatToKv0 k)⁻¹ • x : Unitary.OmegaPt) : Wv v0) =
      wAct v0 (jhatToKv0 k) x := fun x => by
    rw [Unitary.coe_smul_OmegaPt, inv_inv]
  refine or_congr ⟨fun h => Subtype.ext (by rw [hpk, hpk', h]), fun h => ?_⟩ ?_
  · have h2 := congrArg (fun x : Unitary.OmegaPt => wAct v0 (jhatToKv0 k)⁻¹ (x : Wv v0)) h
    simp only [hpk, hpk', wAct_inv_apply] at h2
    exact h2.symm
  · rw [← Unitary.adj_sigmaPt_iff, ← omegaGraph_adj_smul (jhatToKv0 k)⁻¹]
    have h1 : (jhatToKv0 k)⁻¹ • Unitary.sigmaPt = piPt k :=
      Subtype.ext (by rw [hsmul, hpk]; rfl)
    have h2 : (jhatToKv0 k)⁻¹ • piPt m = piPt k' := Subtype.ext (by rw [hsmul, hpk'])
    rw [h1, h2]

end CFSG.Monster.B.TwoA.Amalgam
