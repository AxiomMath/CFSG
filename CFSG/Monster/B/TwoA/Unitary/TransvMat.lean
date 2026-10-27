module

import all CFSG.Fischer.F4
public import CFSG.Monster.B.TwoA.Amalgam.Flag1Planes

public noncomputable section

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer Matrix Module
open CFSG.Monster.B.Classical.UnitarySix (bar bar_bar bar_zero bar_one mul_bar_of_ne_zero)
open CFSG.Monster.B.TwoA.Amalgam (semMap semMap_add semMap_smul semMap_injective hU_semMap
  coe_sigmaAct exists_sigma_rep mem_sigmaAct_iff barPowF barPowF_zero_right sigmaAct_sigmaAct_inv
  e6 e6_ne_zero Rsp suElt finrank_sigmaAct)
open CFSG.Monster.B.Classical.UnitaryPanels (exists_eq_span_singleton_of_finrank_eq_one)

@[expose] def uTransvMat (v : V6) : Matrix (Fin 6) (Fin 6) F4 :=
  1 + vecMulVec (fun i => bar (v (partner i))) v

theorem vecMul_uTransvMat (v x : V6) : x ᵥ* uTransvMat v = x + hU x v • v := by
  rw [uTransvMat, vecMul_add, vecMul_one, vecMul_vecMulVec, hU_eq_sum]
  rfl

theorem det_uTransvMat {v : V6} (hv : hU v v = 0) : (uTransvMat v).det = 1 := by
  rw [uTransvMat, Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have : v ⬝ᵥ (fun i => bar (v (partner i))) = hU v v := by
    rw [hU_eq_sum]
    rfl
  rw [this, hv, add_zero]

theorem hU_vecMul_uTransvMat {v : V6} (hv : hU v v = 0) (x y : V6) :
    hU (x ᵥ* uTransvMat v) (y ᵥ* uTransvMat v) = hU x y := by
  rw [vecMul_uTransvMat, vecMul_uTransvMat]
  simp only [hU_add_left, hU_add_right, hU_smul_left, hU_smul_right, hv, mul_zero, add_zero]
  rw [hU_swap y v]
  linear_combination (hU x v * bar (hU y v)) * F4.two_eq_zero

theorem uTransvMat_smul {c : F4} (hc : c ≠ 0) (v : V6) : uTransvMat (c • v) = uTransvMat v := by
  rw [uTransvMat, uTransvMat]
  congr 1
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    CFSG.Monster.B.Classical.UnitarySix.bar_mul]
  linear_combination (bar (v (partner i)) * v j) * mul_bar_of_ne_zero hc

theorem uTransvMat_mem {v : V6} (hv : hU v v = 0) :
    GeneralLinearGroup.mkOfDetNeZero (uTransvMat v) (by rw [det_uTransvMat hv]; exact one_ne_zero) ∈
      SUh :=
  ⟨det_uTransvMat hv, hU_vecMul_uTransvMat hv⟩

@[expose] def transvSU (v : V6) : SUh := if hv : hU v v = 0 then ⟨_, uTransvMat_mem hv⟩ else 1

theorem coe_transvSU {v : V6} (hv : hU v v = 0) :
    (((transvSU v : SUh) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = uTransvMat v := by
  rw [transvSU, dite_eq_left hv]
  rfl

@[expose] def transvSig (v : V6) : SigmaU6 := suElt (transvSU v)

theorem coe_sigmaAct_transvSig {v : V6} (hv : hU v v = 0) (P : Submodule F4 V6) :
    ((sigmaAct P (transvSig v) : Submodule F4 V6) : Set V6) = (fun x => x + hU x v • v) '' P := by
  have e : transvSig v = ⟨((transvSU v : SUh) : SUh ⧸ Zh), Multiplicative.ofAdd 0⟩ := rfl
  rw [e, coe_sigmaAct]
  congr 1
  funext x
  rw [semMap, coe_transvSU hv, barPowV, ite_eq_left rfl, vecMul_uTransvMat]

theorem hU_smul_self (c : F4) (v : V6) (hc : c ≠ 0) : hU (c • v) (c • v) = hU v v := by
  rw [hU_smul_smul, mul_bar_of_ne_zero hc, one_mul]

theorem transvSU_smul {c : F4} (hc : c ≠ 0) (v : V6) : transvSU (c • v) = transvSU v := by
  by_cases hv : hU v v = 0
  · apply Subtype.ext
    apply Units.ext
    rw [coe_transvSU hv, coe_transvSU ((hU_smul_self c v hc).trans hv), uTransvMat_smul hc]
  · have hcv : ¬hU (c • v) (c • v) = 0 := by rwa [hU_smul_self c v hc]
    rw [transvSU, dite_eq_right hcv, transvSU, dite_eq_right hv]

theorem transvSig_smul {c : F4} (hc : c ≠ 0) (v : V6) : transvSig (c • v) = transvSig v := by
  rw [transvSig, transvSig, transvSU_smul hc]

theorem semMap_transv (g : SUh) (ε : ZMod 2) (v x : V6) :
    semMap g ε (x + hU x v • v) =
      semMap g ε x + hU (semMap g ε x) (semMap g ε v) • semMap g ε v := by
  rw [semMap_add, semMap_smul, hU_semMap]

theorem transvSig_mul_rep
    (g : SUh) (ε : ZMod 2) {v : V6} (hv : hU v v = 0) :
    transvSig v * ⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩ =
      ⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩ * transvSig (semMap g ε v) := by
  have hw : hU (semMap g ε v) (semMap g ε v) = 0 := by
    rw [hU_semMap, hv, barPowF_zero_right]
  have hset : ∀ P : Submodule F4 V6, sigmaAct (sigmaAct P (transvSig v))
      ⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩ =
        sigmaAct (sigmaAct P ⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩)
          (transvSig (semMap g ε v)) := by
    intro P
    apply SetLike.coe_injective
    rw [coe_sigmaAct, coe_sigmaAct_transvSig hv, coe_sigmaAct_transvSig hw, coe_sigmaAct,
      Set.image_image, Set.image_image]
    congr 1
    funext y
    exact semMap_transv g ε v y
  have h1 : (transvSig v * ⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩) *
      (⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩ * transvSig (semMap g ε v))⁻¹ = 1 :=
    eq_one_of_sigmaAct_plane _ fun j =>
      calc sigmaAct (plane j) ((transvSig v * ⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩) *
            (⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩ * transvSig (semMap g ε v))⁻¹)
          = sigmaAct (sigmaAct (plane j)
              (transvSig v * ⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩))
              (⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩ * transvSig (semMap g ε v))⁻¹ :=
            sigmaAct_mul _ _ _
        _ = sigmaAct (sigmaAct (plane j)
              (⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩ * transvSig (semMap g ε v)))
              (⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩ * transvSig (semMap g ε v))⁻¹ := by
            rw [sigmaAct_mul (plane j) (transvSig v), hset, ← sigmaAct_mul (plane j)]
        _ = plane j := sigmaAct_sigmaAct_inv _ _
  exact mul_inv_eq_one.1 h1

theorem transvSig_conj
    {v : V6} (hv : hU v v = 0) (hv0 : v ≠ 0) (x : SigmaU6) :
    ∃ w : V6, w ≠ 0 ∧ w ∈ sigmaAct (Submodule.span F4 {v}) x ∧
      x⁻¹ * transvSig v * x = transvSig w := by
  obtain ⟨g, ε, rfl⟩ := exists_sigma_rep x
  refine ⟨semMap g ε v, fun h => hv0 (semMap_injective g ε (h.trans ?_)),
    mem_sigmaAct_iff.2 ⟨v, Submodule.mem_span_singleton_self v, rfl⟩, ?_⟩
  · have h0 := semMap_smul g ε 0 0
    rw [zero_smul, barPowF_zero_right, zero_smul] at h0
    exact h0.symm
  · rw [mul_assoc, transvSig_mul_rep g ε hv, inv_mul_cancel_left]

open _root_.Classical in
@[expose] def pickVec (R : Submodule F4 V6) : V6 :=
  if h : ∃ v, v ∈ R ∧ v ≠ 0 then Classical.choose h else 0

theorem pickVec_spec {R : Submodule F4 V6} (h : ∃ v, v ∈ R ∧ v ≠ 0) :
    pickVec R ∈ R ∧ pickVec R ≠ 0 := by
  rw [pickVec, dite_eq_left h]
  exact Classical.choose_spec h

@[expose] def transvAt (R : Submodule F4 V6) : SigmaU6 := transvSig (pickVec R)

theorem eq_span_of_isSingPt {R : Submodule F4 V6} (hR : IsSingPt R) {v : V6} (hv : v ∈ R)
    (hv0 : v ≠ 0) : Submodule.span F4 {v} = R :=
  Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hv)
    (by rw [finrank_span_singleton hv0, hR.1])

theorem transvAt_eq {R : Submodule F4 V6} (hR : IsSingPt R) {v : V6} (hv : v ∈ R) (hv0 : v ≠ 0) :
    transvAt R = transvSig v := by
  obtain ⟨hp, hp0⟩ := pickVec_spec ⟨v, hv, hv0⟩
  have hp' : pickVec R ∈ Submodule.span F4 {v} := by
    rw [eq_span_of_isSingPt hR hv hv0]
    exact hp
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hp'
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hp0 hc.symm
  rw [transvAt, ← hc, transvSig_smul hc0]

theorem isotropic_of_isSingPt {R : Submodule F4 V6} (hR : IsSingPt R) {v : V6} (hv : v ∈ R) :
    hU v v = 0 :=
  hR.2 v hv v hv

theorem coe_sigmaAct_transvAt {R : Submodule F4 V6} (hR : IsSingPt R) {v : V6} (hv : v ∈ R)
    (hv0 : v ≠ 0) (P : Submodule F4 V6) :
    ((sigmaAct P (transvAt R) : Submodule F4 V6) : Set V6) = (fun x => x + hU x v • v) '' P := by
  rw [transvAt_eq hR hv hv0, coe_sigmaAct_transvSig (isotropic_of_isSingPt hR hv)]

theorem isSingPt_sigmaAct {R : Submodule F4 V6} (hR : IsSingPt R) (x : SigmaU6) :
    IsSingPt (sigmaAct R x) :=
  CFSG.Monster.B.TwoA.Amalgam.UIso.sigmaAct (d := 1) hR x

theorem transvAt_sigmaAct
    {R : Submodule F4 V6} (hR : IsSingPt R) (x : SigmaU6) :
    transvAt (sigmaAct R x) = x⁻¹ * transvAt R * x := by
  obtain ⟨v, hv0, hRv⟩ := exists_eq_span_singleton_of_finrank_eq_one hR.1
  have hvR : v ∈ R := hRv ▸ Submodule.mem_span_singleton_self v
  obtain ⟨w, hw0, hwR, hconj⟩ := transvSig_conj (isotropic_of_isSingPt hR hvR) hv0 x
  rw [← hRv] at hwR
  rw [transvAt_eq (isSingPt_sigmaAct hR x) hwR hw0, transvAt_eq hR hvR hv0, hconj]

@[expose] def transvU
    (R : Submodule F4 V6) : Usig := phiU.symm (transvAt R)

theorem transvU_sigmaAct
    {R : Submodule F4 V6} (hR : IsSingPt R) (u : Usig) :
    transvU (sigmaAct R (phiU u)) = u⁻¹ * transvU R * u := by
  rw [transvU, transvAt_sigmaAct hR, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  rfl

theorem isSingPt_Rsp :
    IsSingPt Rsp := CFSG.Monster.B.TwoA.Amalgam.uIso_Rsp

theorem transvSig_e6_two : transvSig (e6 2) = slElt 6 := by
  have hiso : hU (e6 2) (e6 2) = 0 := isotropic_of_isSingPt isSingPt_Rsp
    CFSG.Monster.B.TwoA.Amalgam.e6_two_mem_Rsp
  have hc : (fun i => bar (e6 2 (partner i))) = e6 5 := by decide +kernel
  have h : transvSU (e6 2) = b6SU 6 := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_transvSU hiso, coe_b6SU, b6N, CFSG.Monster.B.TwoA.Amalgam.b6Frob_six, barPowM,
      ite_eq_left rfl, CFSG.Monster.B.TwoA.Amalgam.b6Mat_six, uTransvMat, hc]
  rw [transvSig, suElt, h, CFSG.Monster.B.TwoA.Amalgam.slElt_six_eq]
  rfl

theorem transvU_Rsp :
    transvU Rsp = genU 6 := by
  rw [transvU, transvAt_eq isSingPt_Rsp CFSG.Monster.B.TwoA.Amalgam.e6_two_mem_Rsp (e6_ne_zero 2),
    transvSig_e6_two, ← phiU_genU, MulEquiv.symm_apply_apply]

theorem exists_transvU_conj
    {R : Submodule F4 V6} (hR : IsSingPt R) :
    ∃ u : Usig, transvU R = u⁻¹ * genU 6 * u := by
  obtain ⟨H, T, hH, hT, hRH, hHT⟩ := CFSG.Monster.B.TwoA.Amalgam.exists_flag_of_one hR
  obtain ⟨g, h1, -, -⟩ := CFSG.Monster.B.TwoA.Amalgam.exists_SUh_flag hR hH hT hRH hHT
  refine ⟨phiU.symm (suElt g), ?_⟩
  have e : R = sigmaAct Rsp (phiU (phiU.symm (suElt g))) := by
    rw [MulEquiv.apply_symm_apply, h1]
  rw [e, transvU_sigmaAct isSingPt_Rsp, transvU_Rsp]

end CFSG.Monster.B.TwoA.Unitary
