module

public import CFSG.Monster.B.TwoA.Unitary.Transv
public import CFSG.Monster.B.CTIB.Rep4371End
public import CFSG.Monster.B.CTIB.Rep4371Trace

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.CTIB CFSG.Monster.B.Rep4371
open CFSG.Monster.B.Co2 (v0)

theorem coe_basisV23
    (k : Fin 23) : (basisV23 k : Vst) = Rbasis (aIdx k) := by
  rw [basisV23, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.span_apply]

theorem basisV23_repr (x : V23) (k : Fin 23) :
    basisV23.repr x k = Rbasis.repr (x : Vst) (aIdx k) := by
  have h : (Finsupp.lapply k).comp basisV23.repr.toLinearMap =
      (Finsupp.lapply (aIdx k)).comp (Rbasis.repr.toLinearMap.comp V23.subtype) := by
    refine basisV23.ext fun s => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
      Finsupp.lapply_apply, Submodule.subtype_apply, coe_basisV23]
    rw [Finsupp.single_apply, Finsupp.single_apply]
    by_cases hsk : s = k
    · rw [ite_eq_left hsk, ite_eq_left (congrArg aIdx hsk)]
    · rw [ite_eq_right hsk, ite_eq_right (fun h' => hsk (aIdx_injective h'))]
  exact LinearMap.congr_fun h x

theorem trace_resV23
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) :
    LinearMap.trace ℚ V23 (resV23 hh) =
      ∑ k : Fin 23, Rbasis.repr (rhoV h (Rbasis (aIdx k))) (aIdx k) := by
  rw [LinearMap.trace_eq_matrix_trace ℚ basisV23, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, basisV23_repr, resV23,
    LinearMap.coe_restrict_apply, coe_basisV23]
  rfl

theorem trace_resV2048
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) :
    LinearMap.trace ℚ V2048 (resV2048 hh) =
      ∑ t : Fin 2048, Rbasis.repr (rhoV h (Rbasis (tIdx t))) (tIdx t) := by
  rw [LinearMap.trace_eq_matrix_trace ℚ basisV2048, Matrix.trace]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, basisV2048_repr, resV2048,
    LinearMap.coe_restrict_apply, coe_basisV2048]
  rfl

theorem trace_rhoV_eq_add
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) :
    LinearMap.trace ℚ Vst (rhoV h : Vst →ₗ[ℚ] Vst) =
      LinearMap.trace ℚ V23 (resV23 hh) + LinearMap.trace ℚ V2300 (resV2300 hh) +
        LinearMap.trace ℚ V2048 (resV2048 hh) := by
  rw [trace_rhoV, sum_fin_4371, trace_resV23 hh, trace_resV2300 hh, trace_resV2048 hh]
  rfl

theorem trace_resV2048_ne_zero_of_label
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) {u : CVert}
    (hu : (h : Dfull) = clabel u)
    (hfix : {x | x ∈ Unitary.OmegaW ∧ wAct v0 (jhatToKv0 ⟨h, hh⟩) x = x}.ncard < 470) :
    LinearMap.trace ℚ V2048 (resV2048 hh) ≠ 0 := by
  intro h0
  have htr := (trace_rhoV_clabel' u).2 h hu
  rw [trace_rhoV_eq_add hh, h0, add_zero] at htr
  have h23 := abs_trace_resV23_le hh
  have h2300 := abs_trace_resV2300_le hh
  have hfix' : (({x | x ∈ Unitary.OmegaW ∧ wAct v0 (jhatToKv0 ⟨h, hh⟩) x = x}.ncard : ℕ) : ℚ) ≤
      469 := by
    exact_mod_cast Nat.lt_succ_iff.1 hfix
  have hsum := abs_add_le (LinearMap.trace ℚ V23 (resV23 hh))
    (LinearMap.trace ℚ V2300 (resV2300 hh))
  rw [htr] at hsum
  norm_num at hsum
  linarith

theorem coe_resV2048_apply
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) (v : V2048) :
    ((resV2048 hh v : V2048) : Vst) = rhoV h v := rfl

theorem resE_mul_resE_inv (e : Ehat) : resE e * resE e⁻¹ = 1 := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  change rhoV (ehatS e) (rhoV (ehatS e⁻¹) (v : Vst)) = v
  rw [← LinearEquiv.mul_apply, ← map_mul, ← ehatS_mul, mul_inv_cancel, ehatS_one, map_one]
  rfl

theorem resE_inv_mul_resE (e : Ehat) : resE e⁻¹ * resE e = 1 := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  change rhoV (ehatS e⁻¹) (rhoV (ehatS e) (v : Vst)) = v
  rw [← LinearEquiv.mul_apply, ← map_mul, ← ehatS_mul, inv_mul_cancel, ehatS_one, map_one]
  rfl

theorem trace_resV2048_eq_zero_of_conj
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) {e : Ehat}
    (he : (h : Dfull)⁻¹ * e * h = e * xhat) :
    LinearMap.trace ℚ V2048 (resV2048 hh) = 0 := by
  set S := resV2048 hh with hS
  have e1 : ehatS e * h = h * ehatS e * ehatS xhatE := by
    apply Subtype.ext
    change (e : Dfull) * h = h * e * xhat
    calc (e : Dfull) * h = h * ((h : Dfull)⁻¹ * e * h) := by group
      _ = h * e * xhat := by rw [he, mul_assoc]
  have key : S * resE e = (-1 : ℚ) • (resE e * S) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    change rhoV h (rhoV (ehatS e) (v : Vst)) = (-1 : ℚ) • rhoV (ehatS e) (rhoV h (v : Vst))
    calc rhoV h (rhoV (ehatS e) (v : Vst))
        = (-1 : ℚ) • rhoV h (rhoV (ehatS e) (rhoV (ehatS xhatE) (v : Vst))) := by
          rw [rhoV_xhat_V2048 v.2, map_smul, map_smul, smul_smul]
          norm_num
      _ = (-1 : ℚ) • rhoV (h * ehatS e * ehatS xhatE) (v : Vst) := by
          rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      _ = (-1 : ℚ) • rhoV (ehatS e) (rhoV h (v : Vst)) := by
          rw [← e1, map_mul, LinearEquiv.mul_apply]
  have hneg : LinearMap.trace ℚ V2048 S = (-1 : ℚ) * LinearMap.trace ℚ V2048 S :=
    calc LinearMap.trace ℚ V2048 S = LinearMap.trace ℚ V2048 (S * resE e * resE e⁻¹) := by
          rw [mul_assoc, resE_mul_resE_inv, mul_one]
      _ = LinearMap.trace ℚ V2048 (resE e⁻¹ * (S * resE e)) := LinearMap.trace_mul_comm _ _ _
      _ = (-1 : ℚ) * LinearMap.trace ℚ V2048 S := by
          rw [key, mul_smul_comm, map_smul, smul_eq_mul, ← mul_assoc, resE_inv_mul_resE,
            one_mul]
  rw [neg_one_mul, eq_neg_iff_add_eq_zero, ← two_mul] at hneg
  exact (mul_eq_zero.1 hneg).resolve_left two_ne_zero

theorem conj_eq_or_eq_mul_xhat {h : Shat} (hh : (h : Dfull) ∈ Jhat) {e : Ehat}
    (he : wAct v0 (jhatToKv0 ⟨h, hh⟩) (psiW e) = psiW e) :
    (h : Dfull)⁻¹ * e * h = e ∨ (h : Dfull)⁻¹ * e * h = e * xhat := by
  set f : Ehat := ⟨(h : Dfull)⁻¹ * e * h, conj_mem_Ehat hh e.2⟩ with hf
  have hpsi : psiW f = psiW e := (psiW_conj hh e.2).trans he
  have h0 : psiW (e⁻¹ * f) = 0 := by rw [psiW_mul, psiW_inv, hpsi, neg_add_cancel]
  rcases (psiW_eq_zero_iff _).1 h0 with h1 | h1
  · left
    have h2 : f = e := (inv_mul_eq_one.1 h1).symm
    exact congrArg Subtype.val h2
  · right
    have h2 : f = e * xhatE := (inv_mul_eq_iff_eq_mul.1 h1)
    exact congrArg Subtype.val h2

theorem commute_Ehat_of_trace_ne_zero
    {h : Shat} (hh : (h : Dfull) ∈ Jhat)
    (htr : LinearMap.trace ℚ V2048 (resV2048 hh) ≠ 0) {e : Ehat}
    (he : wAct v0 (jhatToKv0 ⟨h, hh⟩) (psiW e) = psiW e) : (h : Dfull) * e = e * h := by
  rcases conj_eq_or_eq_mul_xhat hh he with h1 | h1
  · calc (h : Dfull) * e = h * ((h : Dfull)⁻¹ * e * h) := by rw [h1]
      _ = e * h := by group
  · exact absurd (trace_resV2048_eq_zero_of_conj hh h1) htr

theorem commute_Ehat_of_label
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) {u : CVert}
    (hu : (h : Dfull) = clabel u)
    (hfix : {x | x ∈ Unitary.OmegaW ∧ wAct v0 (jhatToKv0 ⟨h, hh⟩) x = x}.ncard < 470)
    {e : Ehat} (he : wAct v0 (jhatToKv0 ⟨h, hh⟩) (psiW e) = psiW e) :
    (h : Dfull) * e = e * h :=
  commute_Ehat_of_trace_ne_zero hh (trace_resV2048_ne_zero_of_label hh hu hfix) he

theorem distThree_trace_bridge
    {s : Dfull} (hs : s ∈ Jhat) {u : CVert} (hu : s = clabel u)
    {R : Submodule CFSG.Fischer.F4 Unitary.V6} (hR : Unitary.IsSingPt R)
    (hsR : jhatToKv0 ⟨s, hs⟩ = (Unitary.transvU R : Kstab v0)) {r : Ehat}
    (hr : wAct v0 (Unitary.transvU R) (psiW r) = psiW r) : s * r = r * s := by
  have hfix : {x | x ∈ Unitary.OmegaW ∧
      wAct v0 (jhatToKv0 ⟨(⟨s, Jhat_le_Shat hs⟩ : Shat), hs⟩) x = x}.ncard < 470 := by
    change {x | x ∈ Unitary.OmegaW ∧ wAct v0 (jhatToKv0 ⟨s, hs⟩) x = x}.ncard < 470
    rw [hsR, Unitary.ncard_fix_OmegaW_transvU hR]
    norm_num
  have he : wAct v0 (jhatToKv0 ⟨(⟨s, Jhat_le_Shat hs⟩ : Shat), hs⟩) (psiW r) = psiW r := by
    change wAct v0 (jhatToKv0 ⟨s, hs⟩) (psiW r) = psiW r
    rw [hsR]
    exact hr
  exact commute_Ehat_of_label (h := ⟨s, Jhat_le_Shat hs⟩) hs hu hfix he

theorem distThree_trace_bridge_base
    {s : Dfull} (hs : s ∈ P1) {u : CVert} (hu : s = clabel u)
    {R : Submodule CFSG.Fischer.F4 Unitary.V6} (hR : R ∈ Unitary.ptOrbit 0)
    (hsR : p1Proj ⟨s, hs⟩ = Unitary.transvU R) {r : Ehat} (hr : psiW r = Unitary.tauW) :
    s * r = r * s := by
  have hR' : R ∈ Unitary.fixTauPts := by
    rw [Unitary.fixTauPts_eq]
    exact hR
  refine distThree_trace_bridge (P1_le_Jhat hs) hu hR'.1 ?_ (by rw [hr]; exact hR'.2)
  rw [← coe_p1Proj ⟨s, hs⟩, hsR]

end CFSG.Monster.B.TwoA.Amalgam
