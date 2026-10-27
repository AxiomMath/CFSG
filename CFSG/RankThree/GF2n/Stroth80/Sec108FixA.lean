module

public import CFSG.RankThree.GF2n.Stroth80.Sec108SLComm
public import CFSG.RankThree.GF2n.Stroth80.Sec108Norm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

private theorem phi_inv_fix (AM : Smith81.Smith23E1.ActionModel M Q Z) {m : ↥(H0 M Z)}
    (hm : ∀ e ∈ AM.Vsp hc t, AM.φ m e = e) :
    ∀ e ∈ AM.Vsp hc t, AM.φ m⁻¹ e = e := by
  intro e he
  calc AM.φ m⁻¹ e = AM.φ m⁻¹ (AM.φ m e) := by rw [hm e he]
    _ = e := by
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl

private theorem phi_mul_inv_apply (AM : Smith81.Smith23E1.ActionModel M Q Z) (m : ↥(H0 M Z))
    (x : AM.M₀.E) : AM.φ m (AM.φ m⁻¹ x) = x := by
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

private theorem comm_inv (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {m : ↥(H0 M Z)}
    (hm : ∀ e, AM.φ m (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m e)) :
    ∀ e, AM.φ m⁻¹ (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m⁻¹ e) := by
  intro e
  have h := hm (AM.φ m⁻¹ e)
  rw [phi_mul_inv_apply AM m] at h
  apply (AM.φ m).injective
  rw [phi_mul_inv_apply AM m, h]

private theorem fix_Vsp_of_comm_Vt (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G}
    (hd : d ∈ H0 M Z) (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z) :
    ∀ e ∈ AM.Vsp hc t, AM.φ ⟨d, hd⟩ e = e := by
  intro e he
  obtain ⟨v, hvV, hvQ, hv⟩ := AM.M₀.mem_img.mp (mem_imgSub.mp he)
  rw [← hv]
  exact (comm_mem_iff_fix (M₀ := AM.M₀) (T := AM.φ ⟨d, hd⟩)
    (hc.conj_mem_Q_of_mem_M hd.1).1 (fun z hz => AM.φ_π ⟨d, hd⟩ z hz)
    (hc.Vt_le_Q t hvV)).mp (hdV v hvV)

theorem Sec108Data.comm_mem_CN_of_fix (D : Sec108Data hc t Y) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) : ⁅r, d⁆ ∈ hc.CN t := by
  have hrH : r ∈ H0 M Z := D.Rt_le_H0 hr
  have hdR : d ∈ Subgroup.normalizer ((Rt M (LB M Q B) t : Subgroup G) : Set G) :=
    (D.mem_normalizer_root_iff_Rt hd.1).mp hdY
  have hdr : d * r⁻¹ * d⁻¹ ∈ Rt M (LB M Q B) t :=
    (Subgroup.mem_normalizer_iff.mp hdR r⁻¹).mp (Subgroup.inv_mem _ hr)
  have hr' : ⁅r, d⁆ ∈ Rt M (LB M Q B) t := by
    rw [commutatorElement_def]
    simpa only [mul_assoc] using Subgroup.mul_mem (Rt M (LB M Q B) t) hr hdr
  refine Ctx.mem_CN.mpr ⟨hr', fun v hv => ?_⟩
  obtain ⟨AM⟩ := Smith81.Smith23E1.ActionModel.nonempty hc.hyp
  have hfixd : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨d, hd⟩ e = e := fix_Vsp_of_comm_Vt AM hd hdV
  have hcommH : ⁅r, d⁆ ∈ H0 M Z := D.Rt_le_H0 hr'
  have hfix : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨⁅r, d⁆, hcommH⟩ e = e := by
    intro e he
    have hde : AM.φ ⟨d, hd⟩⁻¹ e = e := by
      calc AM.φ ⟨d, hd⟩⁻¹ e = AM.φ ⟨d, hd⟩⁻¹ (AM.φ ⟨d, hd⟩ e) := by rw [hfixd e he]
        _ = e := by
          rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl
    have hrinv : AM.φ ⟨r, hrH⟩⁻¹ e ∈ AM.Vsp hc t :=
      D.phi_mem_Vsp AM (Subgroup.inv_mem _ hr) he
    have hsub : (⟨⁅r, d⁆, hcommH⟩ : ↥(H0 M Z)) =
        ⟨r, hrH⟩ * ⟨d, hd⟩ * ⟨r, hrH⟩⁻¹ * ⟨d, hd⟩⁻¹ := by
      refine Subtype.ext ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
      rw [commutatorElement_def]
    rw [hsub]
    simp only [map_mul, LinearEquiv.mul_apply]
    rw [hde, hfixd _ hrinv, phi_mul_inv_apply]
  exact hc.comm_Vt_of_fix AM hcommH hfix v hv

private theorem phiMat_sqrtDiag_fix (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z)
    (hV : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨d, hd⟩ e = e)
    (ht : ∀ e, AM.φ ⟨d, hd⟩ (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨d, hd⟩ e))
    (A : Matrix.SpecialLinearGroup (Fin 3) AM.K) :
    (A : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ
        CFSG.LinearAlgebra.sqrtDiag (D.phiMat AM ⟨d, hd⟩) =
      CFSG.LinearAlgebra.sqrtDiag (D.phiMat AM ⟨d, hd⟩) := by
  obtain ⟨r, ⟨hrR, hrt⟩, hrH, hrA⟩ := D.bV_spec AM A
  have hcomm_rt : ⁅r, t⁆ ∈ Q := by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hrt)]
    exact Q.one_mem
  have hrT : ∀ e, AM.φ ⟨r, hrH⟩ (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨r, hrH⟩ e) := Sec108Data.phi_comm_of_comm_mem AM hcomm_rt
  have hconj := D.phiMat_conj AM (r := ⟨r, hrH⟩) (m := ⟨d, hd⟩) hrT hrA hV ht
  have hcomm_mem : ⁅r, d⁆ ∈ hc.CN t := D.comm_mem_CN_of_fix hd hdY hdV hrR
  have hcommH : ⁅r, d⁆ ∈ H0 M Z := D.CN_le_H0 hcomm_mem
  have hVc : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨⁅r, d⁆, hcommH⟩ e = e := fun e he =>
    D.fix_Vsp_of_mem_CN AM hcomm_mem he
  have htc : ∀ e, AM.φ ⟨⁅r, d⁆, hcommH⟩ (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨⁅r, d⁆, hcommH⟩ e) := fun e =>
    D.comm_t_of_mem_CN AM hcomm_mem e
  have hdecomp : (⟨r, hrH⟩ * ⟨d, hd⟩ * ⟨r, hrH⟩⁻¹ : ↥(H0 M Z)) =
      ⟨⁅r, d⁆, hcommH⟩ * ⟨d, hd⟩ := by
    refine Subtype.ext ?_
    show r * d * r⁻¹ = ⁅r, d⁆ * d
    rw [commutatorElement_def]
    group
  have hsum : D.phiMat AM (⟨⁅r, d⁆, hcommH⟩ * ⟨d, hd⟩) =
      D.phiMat AM ⟨⁅r, d⁆, hcommH⟩ + D.phiMat AM ⟨d, hd⟩ :=
    D.phiMat_mul AM (m := ⟨⁅r, d⁆, hcommH⟩) (m' := ⟨d, hd⟩) hVc hV ht
  have hzeroC : CFSG.LinearAlgebra.sqrtDiag (D.phiMat AM ⟨⁅r, d⁆, hcommH⟩) = 0 :=
    (CFSG.LinearAlgebra.sqrtDiag_eq_zero_iff _).mpr fun j => D.phiMat_diag AM hcomm_mem j
  have hS : (D.phiMat AM ⟨d, hd⟩)ᵀ = D.phiMat AM ⟨d, hd⟩ := D.phiMat_transpose AM hV ht
  calc (A : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ
        CFSG.LinearAlgebra.sqrtDiag (D.phiMat AM ⟨d, hd⟩)
      = CFSG.LinearAlgebra.sqrtDiag ((A : Matrix (Fin 3) (Fin 3) AM.K) *
          D.phiMat AM ⟨d, hd⟩ * (A : Matrix (Fin 3) (Fin 3) AM.K)ᵀ) :=
        (CFSG.LinearAlgebra.sqrtDiag_mul_mul_transpose hS _).symm
    _ = CFSG.LinearAlgebra.sqrtDiag
          (D.phiMat AM (⟨r, hrH⟩ * ⟨d, hd⟩ * ⟨r, hrH⟩⁻¹)) := by rw [← hconj]
    _ = CFSG.LinearAlgebra.sqrtDiag
          (D.phiMat AM (⟨⁅r, d⁆, hcommH⟩ * ⟨d, hd⟩)) := by rw [hdecomp]
    _ = CFSG.LinearAlgebra.sqrtDiag (D.phiMat AM ⟨⁅r, d⁆, hcommH⟩) +
          CFSG.LinearAlgebra.sqrtDiag (D.phiMat AM ⟨d, hd⟩) := by
        rw [hsum, CFSG.LinearAlgebra.sqrtDiag_add]
    _ = CFSG.LinearAlgebra.sqrtDiag (D.phiMat AM ⟨d, hd⟩) := by rw [hzeroC, zero_add]

theorem Sec108Data.phiMat_diag_of_fix (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z) (hdt : ⁅d, t⁆ ∈ Q) (i : Fin 3) :
    D.phiMat AM ⟨d, hd⟩ i i = 0 := by
  have hV : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨d, hd⟩ e = e := fix_Vsp_of_comm_Vt AM hd hdV
  have ht : ∀ e, AM.φ ⟨d, hd⟩ (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨d, hd⟩ e) := Sec108Data.phi_comm_of_comm_mem AM hdt
  have hzero : CFSG.LinearAlgebra.sqrtDiag (D.phiMat AM ⟨d, hd⟩) = 0 := by
    apply CFSG.LinearAlgebra.eq_zero_of_forall_specialLinear_mulVec_eq
    intro A
    exact phiMat_sqrtDiag_fix D AM hd hdY hdV hV ht A
  exact (CFSG.LinearAlgebra.sqrtDiag_eq_zero_iff _).mp hzero i

theorem Sec108Data.exists_CN_fix_U (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z) (hdt : ⁅d, t⁆ ∈ Q) :
    ∃ n ∈ hc.CN t, ∃ h1 : n⁻¹ * d ∈ H0 M Z,
      ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨n⁻¹ * d, h1⟩ u = u := by
  have hVd : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨d, hd⟩ e = e := fix_Vsp_of_comm_Vt AM hd hdV
  have htd : ∀ e, AM.φ ⟨d, hd⟩ (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨d, hd⟩ e) := Sec108Data.phi_comm_of_comm_mem AM hdt
  have hS : (D.phiMat AM ⟨d, hd⟩)ᵀ = D.phiMat AM ⟨d, hd⟩ := D.phiMat_transpose AM hVd htd
  have hd0 : ∀ i, D.phiMat AM ⟨d, hd⟩ i i = 0 := fun i =>
    D.phiMat_diag_of_fix AM hd hdY hdV hdt i
  obtain ⟨n, hn, hnS⟩ := D.exists_phiMat_eq AM (D.phiMat AM ⟨d, hd⟩) hS hd0
  set nH : ↥(H0 M Z) := ⟨n, D.CN_le_H0 hn⟩ with hnH
  set dH : ↥(H0 M Z) := ⟨d, hd⟩ with hdH
  have hVn : ∀ e ∈ AM.Vsp hc t, AM.φ nH e = e := fun e he => D.fix_Vsp_of_mem_CN AM hn he
  have hVni : ∀ e ∈ AM.Vsp hc t, AM.φ nH⁻¹ e = e := phi_inv_fix AM hVn
  have htn : ∀ e, AM.φ nH (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ nH e) := fun e => D.comm_t_of_mem_CN AM hn e
  have htni : ∀ e, AM.φ nH⁻¹ (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ nH⁻¹ e) := comm_inv D AM htn
  have hV : ∀ e ∈ AM.Vsp hc t, AM.φ (nH⁻¹ * dH) e = e := by
    intro e he
    rw [map_mul, LinearEquiv.mul_apply, hVd e he, hVni e he]
  have ht : ∀ e, AM.φ (nH⁻¹ * dH) (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ (nH⁻¹ * dH) e) := by
    intro e
    simp only [map_mul, LinearEquiv.mul_apply, htd, htni]
  have hnn : D.phiMat AM (nH * nH⁻¹) = D.phiMat AM nH + D.phiMat AM nH⁻¹ :=
    D.phiMat_mul AM (m := nH) (m' := nH⁻¹) hVn hVni htni
  have hone : D.phiMat AM (1 : ↥(H0 M Z)) = 0 := by
    ext j l
    simp [D.phiMat_apply]
  have hnn' : D.phiMat AM (nH * nH⁻¹) = 0 := by
    rw [mul_inv_cancel]
    exact hone
  have hneg : D.phiMat AM nH⁻¹ = -D.phiMat AM nH :=
    eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hnn.symm.trans hnn')
  have hm0 : D.phiMat AM (nH⁻¹ * dH) = 0 := by
    rw [D.phiMat_mul AM (m := nH⁻¹) (m' := dH) hVni hVd htd, hneg, hnS]
    abel
  exact ⟨n, hn, (nH⁻¹ * dH).2, fun u hu =>
    (D.phiMat_eq_zero_iff AM (m := nH⁻¹ * dH) hV ht).mp hm0 u hu⟩

end CFSG.RankThree.GF2n.Stroth80
