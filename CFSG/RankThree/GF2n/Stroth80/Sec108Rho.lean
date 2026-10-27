module

public import CFSG.RankThree.GF2n.Stroth80.Sec108BarLift
public import CFSG.RankThree.GF2n.Stroth80.Sec108Levi
public import CFSG.RankThree.GF2n.Stroth80.Sec108SLComm
public import CFSG.RankThree.GF2n.Stroth80.Sec103ATools

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

theorem Ctx.four_le_card_K (hc : Ctx M Q Z B) (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    4 ≤ Nat.card AM.K := by
  rw [AM.glob.card]
  exact hc.hyp.q4

theorem Sec108Data.root_le_CN (D : Sec108Data hc t Y) : Y ≤ hc.CN t := by
  rw [D.CN_eq]
  intro y hy
  exact Subgroup.mem_sup_right ⟨CFSG.RankThree.GF2n.Stroth80.Sit.le_QB D.sit hy,
    (Subgroup.mem_inf.mp ((smith_1_12 D.sit).1 hy)).1⟩

theorem Sec108Data.bar_root_le_centralizer [(Q.subgroupOf M).Normal] (D : Sec108Data hc t Y) :
    bar M Q Y ≤ Subgroup.centralizer (bar M Q (Rt M (LB M Q B) t) : Set (Mbar M Q)) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  obtain ⟨g, hgY, hgM, rfl⟩ := (HS6.mem_bar y).mp hy
  obtain ⟨h, hhR, hhM, rfl⟩ := (HS6.mem_bar r).mp hr
  exact HS6.piM_comm_of_comm_mem hhM hgM (D.comm_Rt_root_mem h hhR g hgY)

private theorem e₀_ne_zero (K : Type) [Field K] : Sec108.e₀ K ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simpa [Sec108.e₀] using h0

private theorem exists_sl_mulVec_eq {K : Type} [Field K] {x y : Fin 3 → K}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ P : Matrix.SpecialLinearGroup (Fin 3) K,
      (P : Matrix (Fin 3) (Fin 3) K) *ᵥ x = y := by
  obtain ⟨A, hA, hAy⟩ :=
    CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq (m := 3) (by norm_num) hx hy
  exact ⟨⟨(A : Matrix (Fin 3) (Fin 3) K),
    CFSG.Open.StatedAPI.mem_statedSL_iff.mp hA⟩, hAy⟩

private theorem sl_inv_coe {K : Type} [Field K]
    (P : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((P : Matrix (Fin 3) (Fin 3) K))⁻¹ := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  exact (Matrix.inv_eq_right_inv
    (by rw [Matrix.mul_adjugate, P.2, one_smul])).symm

private theorem sl_inv_mul {K : Type} [Field K]
    (P : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (P : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [sl_inv_coe P]
  exact Matrix.nonsing_inv_mul (P : Matrix (Fin 3) (Fin 3) K)
    (by rw [Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one)

private theorem sl_conj_mul {K : Type} [Field K]
    (P : Matrix.SpecialLinearGroup (Fin 3) K) (A B : Matrix (Fin 3) (Fin 3) K) :
    ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (A * B) * (P : Matrix (Fin 3) (Fin 3) K) =
      (((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A *
          (P : Matrix (Fin 3) (Fin 3) K)) *
        (((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B *
          (P : Matrix (Fin 3) (Fin 3) K)) := by
  rw [sl_inv_coe P]
  have hP : IsUnit ((P : Matrix (Fin 3) (Fin 3) K).det) := by
    rw [Matrix.SpecialLinearGroup.det_coe]
    exact isUnit_one
  have h1 : (P : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv (P : Matrix (Fin 3) (Fin 3) K) hP
  simp only [mul_assoc]
  rw [← mul_assoc (P : Matrix (Fin 3) (Fin 3) K) (P : Matrix (Fin 3) (Fin 3) K)⁻¹
    (B * (P : Matrix (Fin 3) (Fin 3) K)), h1, one_mul]

private theorem sl_conj_eq_one {K : Type} [Field K]
    (P : Matrix.SpecialLinearGroup (Fin 3) K) {A : Matrix (Fin 3) (Fin 3) K}
    (h : ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A *
      (P : Matrix (Fin 3) (Fin 3) K) = 1) : A = 1 := by
  rw [sl_inv_coe P] at h
  have hP : IsUnit ((P : Matrix (Fin 3) (Fin 3) K).det) := by
    rw [Matrix.SpecialLinearGroup.det_coe]
    exact isUnit_one
  have h1 : (P : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv (P : Matrix (Fin 3) (Fin 3) K) hP
  have h2 : (P : Matrix (Fin 3) (Fin 3) K) * ((P : Matrix (Fin 3) (Fin 3) K)⁻¹ * A *
      (P : Matrix (Fin 3) (Fin 3) K)) * (P : Matrix (Fin 3) (Fin 3) K)⁻¹ = A := by
    rw [mul_assoc (P : Matrix (Fin 3) (Fin 3) K)⁻¹ A (P : Matrix (Fin 3) (Fin 3) K),
      Matrix.mul_nonsing_inv_cancel_left (A := (P : Matrix (Fin 3) (Fin 3) K))
        (B := A * (P : Matrix (Fin 3) (Fin 3) K)) hP,
      Matrix.mul_nonsing_inv_cancel_right (B := A) (A := (P : Matrix (Fin 3) (Fin 3) K)) hP]
  rw [← h2, h, mul_one, h1]

private theorem sl_conj_apply {K : Type} [Field K]
    (P : Matrix.SpecialLinearGroup (Fin 3) K) (B : Matrix (Fin 3) (Fin 3) K) :
    ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((P : Matrix (Fin 3) (Fin 3) K) * B *
          ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        (P : Matrix (Fin 3) (Fin 3) K) = B := by
  rw [sl_inv_coe P]
  have hP : IsUnit ((P : Matrix (Fin 3) (Fin 3) K).det) := by
    rw [Matrix.SpecialLinearGroup.det_coe]
    exact isUnit_one
  calc
    (P : Matrix (Fin 3) (Fin 3) K)⁻¹ *
        ((P : Matrix (Fin 3) (Fin 3) K) * B * (P : Matrix (Fin 3) (Fin 3) K)⁻¹) *
        (P : Matrix (Fin 3) (Fin 3) K) =
      ((P : Matrix (Fin 3) (Fin 3) K)⁻¹ *
        ((P : Matrix (Fin 3) (Fin 3) K) *
          (B * (P : Matrix (Fin 3) (Fin 3) K)⁻¹))) *
        (P : Matrix (Fin 3) (Fin 3) K) := by
      rw [mul_assoc (P : Matrix (Fin 3) (Fin 3) K) B (P : Matrix (Fin 3) (Fin 3) K)⁻¹]
    _ = (B * (P : Matrix (Fin 3) (Fin 3) K)⁻¹) * (P : Matrix (Fin 3) (Fin 3) K) := by
      rw [Matrix.nonsing_inv_mul_cancel_left (A := (P : Matrix (Fin 3) (Fin 3) K))
        (B := B * (P : Matrix (Fin 3) (Fin 3) K)⁻¹) hP]
    _ = B := by
      rw [Matrix.nonsing_inv_mul_cancel_right (B := B) (A := (P : Matrix (Fin 3) (Fin 3) K)) hP]

section Rho

variable (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)

theorem Sec108Data.exists_frameB :
    ∃ P : Matrix.SpecialLinearGroup (Fin 3) AM.K,
      ∑ i, ((P : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ Sec108.e₀ AM.K) i • (D.bV AM i : AM.M₀.E) ∈
        D.Bsp AM := by
  obtain ⟨β, hβ, hβB⟩ := D.exists_coord_Bsp AM
  obtain ⟨P, hP⟩ := exists_sl_mulVec_eq (e₀_ne_zero AM.K) hβ
  exact ⟨P, by rw [hP]; exact hβB⟩

noncomputable def Sec108Data.frameB : Matrix.SpecialLinearGroup (Fin 3) AM.K :=
  (D.exists_frameB AM).choose

theorem Sec108Data.frameB_mem_Bsp :
    ∑ i, ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ Sec108.e₀ AM.K) i •
      (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM :=
  (D.exists_frameB AM).choose_spec

@[expose] noncomputable def Sec108Data.rhoMat (r : ↥(Rt M (LB M Q B) t)) :
    Matrix (Fin 3) (Fin 3) AM.K :=
  (((D.frameB AM)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) AM.K) : Matrix (Fin 3) (Fin 3) AM.K) *
    D.matV AM ⟨r, D.Rt_le_H0 r.2⟩ * (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)

private theorem rhoMat_eq_one_of_matV_eq_one (r : ↥(Rt M (LB M Q B) t))
    (h : D.matV AM ⟨(r : G), D.Rt_le_H0 r.2⟩ = 1) : D.rhoMat AM r = 1 := by
  rw [Sec108Data.rhoMat, h, mul_one]
  exact sl_inv_mul (D.frameB AM)

private theorem matV_eq_one_of_rhoMat_eq_one (r : ↥(Rt M (LB M Q B) t))
    (h : D.rhoMat AM r = 1) :
    D.matV AM ⟨(r : G), D.Rt_le_H0 r.2⟩ = 1 :=
  sl_conj_eq_one (D.frameB AM) h

theorem Sec108Data.rhoMat_one : D.rhoMat AM 1 = 1 := by
  have h1 : (⟨((1 : ↥(Rt M (LB M Q B) t)) : G), D.Rt_le_H0 (1 : ↥(Rt M (LB M Q B) t)).2⟩ :
      ↥(H0 M Z)) = 1 := Subtype.ext rfl
  rw [Sec108Data.rhoMat, h1, D.matV_one AM, mul_one]
  exact sl_inv_mul (D.frameB AM)

theorem Sec108Data.rhoMat_mul (r r' : ↥(Rt M (LB M Q B) t)) :
    D.rhoMat AM (r * r') = D.rhoMat AM r * D.rhoMat AM r' := by
  have hEq : (⟨((r * r' : ↥(Rt M (LB M Q B) t)) : G),
      D.Rt_le_H0 (r * r').2⟩ : ↥(H0 M Z)) =
      ⟨(r : G), D.Rt_le_H0 r.2⟩ * ⟨(r' : G), D.Rt_le_H0 r'.2⟩ := Subtype.ext rfl
  have hmul := D.matV_mul AM (m := ⟨(r : G), D.Rt_le_H0 r.2⟩)
    (m' := ⟨(r' : G), D.Rt_le_H0 r'.2⟩) (fun e he => D.phi_mem_Vsp AM r'.2 he)
  rw [Sec108Data.rhoMat, Sec108Data.rhoMat, Sec108Data.rhoMat, hEq, hmul]
  exact sl_conj_mul (D.frameB AM) _ _

noncomputable def Sec108Data.rho₀ : ↥(Rt M (LB M Q B) t) →* GL (Fin 3) AM.K :=
  MonoidHom.toHomUnits
    ({ toFun := D.rhoMat AM
       map_one' := D.rhoMat_one AM
       map_mul' := D.rhoMat_mul AM } : ↥(Rt M (LB M Q B) t) →* Matrix (Fin 3) (Fin 3) AM.K)

private theorem coe_rho₀ (r : ↥(Rt M (LB M Q B) t)) :
    ((D.rho₀ AM r : GL (Fin 3) AM.K) : Matrix (Fin 3) (Fin 3) AM.K) = D.rhoMat AM r := rfl

private theorem det_rhoMat_eq_one (r : ↥(Rt M (LB M Q B) t)) :
    (D.rhoMat AM r).det = 1 := by
  rw [Sec108Data.rhoMat, Matrix.det_mul, Matrix.det_mul,
    Matrix.SpecialLinearGroup.det_coe ((D.frameB AM)⁻¹),
    Matrix.SpecialLinearGroup.det_coe (D.frameB AM), D.det_matV_eq_one AM r.2]
  norm_num

theorem Sec108Data.rho₀_eq_one (r : ↥(Rt M (LB M Q B) t)) (hr : (r : G) ∈ Q) :
    D.rho₀ AM r = 1 := by
  have hm : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨(r : G), D.Rt_le_H0 r.2⟩ e ∈ AM.Vsp hc t :=
    fun e he => D.phi_mem_Vsp AM r.2 he
  have hfix : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨(r : G), D.Rt_le_H0 r.2⟩ e = e := by
    intro e he
    rw [(AM.φ_ker _).mpr hr]
    rfl
  have hmat : D.matV AM ⟨(r : G), D.Rt_le_H0 r.2⟩ = 1 :=
    (D.matV_eq_one_iff AM hm).mpr hfix
  refine Units.ext ?_
  change ((D.rho₀ AM r : GL (Fin 3) AM.K) : Matrix (Fin 3) (Fin 3) AM.K) = 1
  rw [coe_rho₀]
  exact rhoMat_eq_one_of_matV_eq_one D AM r hmat

variable [(Q.subgroupOf M).Normal]

noncomputable def Sec108Data.rho : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL (Fin 3) AM.K :=
  barLift (D.rho₀ AM) (D.rho₀_eq_one AM)

theorem Sec108Data.rho_piM {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (h : HS6.piM M Q r ∈ bar M Q (Rt M (LB M Q B) t)) :
    ((D.rho AM ⟨HS6.piM M Q r, h⟩ : GL (Fin 3) AM.K) : Matrix (Fin 3) (Fin 3) AM.K) =
      D.rhoMat AM ⟨r, hr⟩ := by
  have hrho : D.rho AM ⟨HS6.piM M Q r, h⟩ = D.rho₀ AM ⟨r, hr⟩ := by
    show barLift (D.rho₀ AM) (D.rho₀_eq_one AM) ⟨HS6.piM M Q r, h⟩ = D.rho₀ AM ⟨r, hr⟩
    exact barLift_piM (D.rho₀ AM) (D.rho₀_eq_one AM) ⟨r, hr⟩ (hc.Rt_le_M t hr) h
  rw [hrho, coe_rho₀]

private theorem matV_eq_one_of_mem_CN {n : G} (hn : n ∈ hc.CN t) :
    D.matV AM ⟨n, D.Rt_le_H0 (Ctx.mem_CN.mp hn).1⟩ = 1 := by
  have hR := (Ctx.mem_CN.mp hn).1
  refine (D.matV_eq_one_iff AM (m := ⟨n, D.Rt_le_H0 hR⟩)
    (fun e he => D.phi_mem_Vsp AM hR he)).mpr ?_
  intro e he
  exact D.fix_Vsp_of_mem_CN AM hn he

private theorem coe_rho_eq_rhoMat_barRep (x : ↥(bar M Q (Rt M (LB M Q B) t))) :
    ((D.rho AM x : GL (Fin 3) AM.K) : Matrix (Fin 3) (Fin 3) AM.K) =
      D.rhoMat AM (barRep x) := by
  have hmem : HS6.piM M Q (barRep x : G) ∈ bar M Q (Rt M (LB M Q B) t) := by
    rw [piM_barRep x]
    exact x.2
  have h := D.rho_piM AM (r := (barRep x : G)) (barRep x).2 hmem
  have hx : (⟨HS6.piM M Q (barRep x : G), hmem⟩ :
      ↥(bar M Q (Rt M (LB M Q B) t))) = x := Subtype.ext (piM_barRep x)
  rwa [hx] at h

theorem Sec108Data.range_rho : (D.rho AM).range = StatedSL 3 AM.K := by
  apply le_antisymm
  · intro A hA
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hA
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
    rw [coe_rho_eq_rhoMat_barRep D AM x]
    exact det_rhoMat_eq_one D AM (barRep x)
  · intro C hC
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff] at hC
    let A' : Matrix.SpecialLinearGroup (Fin 3) AM.K :=
      ⟨(D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) * (C : Matrix (Fin 3) (Fin 3) AM.K) *
        (((D.frameB AM)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) AM.K) :
          Matrix (Fin 3) (Fin 3) AM.K), by
        rw [Matrix.det_mul, Matrix.det_mul,
          Matrix.SpecialLinearGroup.det_coe ((D.frameB AM)⁻¹),
          Matrix.SpecialLinearGroup.det_coe (D.frameB AM), hC]
        norm_num⟩
    obtain ⟨r, ⟨hrR, -⟩, hrH, hrmat⟩ := D.bV_spec AM A'
    have hmatV : D.matV AM ⟨r, D.Rt_le_H0 hrR⟩ = A' := by
      rw [show (⟨r, D.Rt_le_H0 hrR⟩ : ↥(H0 M Z)) = ⟨r, hrH⟩ from Subtype.ext rfl]
      exact D.matV_eq_of_forall AM (m := ⟨r, hrH⟩) hrmat
    have hmem : HS6.piM M Q r ∈ bar M Q (Rt M (LB M Q B) t) :=
      HS6.piM_mem_bar hrR (hc.Rt_le_M t hrR)
    refine ⟨⟨HS6.piM M Q r, hmem⟩, ?_⟩
    have hrho : D.rho AM ⟨HS6.piM M Q r, hmem⟩ = D.rho₀ AM ⟨r, hrR⟩ := by
      show barLift (D.rho₀ AM) (D.rho₀_eq_one AM) ⟨HS6.piM M Q r, hmem⟩ =
        D.rho₀ AM ⟨r, hrR⟩
      exact barLift_piM (D.rho₀ AM) (D.rho₀_eq_one AM) ⟨r, hrR⟩ (hc.Rt_le_M t hrR) hmem
    rw [hrho]
    refine Units.ext ?_
    change ((D.rho₀ AM ⟨r, hrR⟩ : GL (Fin 3) AM.K) : Matrix (Fin 3) (Fin 3) AM.K) =
      (C : Matrix (Fin 3) (Fin 3) AM.K)
    rw [coe_rho₀, Sec108Data.rhoMat, hmatV]
    exact sl_conj_apply (D.frameB AM) (C : Matrix (Fin 3) (Fin 3) AM.K)

theorem Sec108Data.ker_rho :
    (D.rho AM).ker = (bar M Q (hc.CN t)).subgroupOf (bar M Q (Rt M (LB M Q B) t)) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    have hmat : D.rhoMat AM (barRep x) = 1 := by
      rw [← coe_rho_eq_rhoMat_barRep D AM x, hx]
      rfl
    have hfix : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨(barRep x : G), D.Rt_le_H0 (barRep x).2⟩ e = e :=
      (D.matV_eq_one_iff AM (m := ⟨(barRep x : G), D.Rt_le_H0 (barRep x).2⟩)
        (fun e he => D.phi_mem_Vsp AM (barRep x).2 he)).mp
        (matV_eq_one_of_rhoMat_eq_one D AM (barRep x) hmat)
    have hCN : (barRep x : G) ∈ hc.CN t :=
      Ctx.mem_CN.mpr ⟨(barRep x).2,
        Ctx.comm_Vt_of_fix hc AM (D.Rt_le_H0 (barRep x).2) hfix⟩
    rw [Subgroup.mem_subgroupOf, ← piM_barRep x]
    exact HS6.piM_mem_bar hCN (barRep_mem x)
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨n, hnCN, hnM, hn⟩ := (HS6.mem_bar (x : Mbar M Q)).mp hx
    have hnR : n ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hnCN).1
    have hmem : HS6.piM M Q n ∈ bar M Q (Rt M (LB M Q B) t) := by
      rw [hn]
      exact x.2
    have hx' : (⟨HS6.piM M Q n, hmem⟩ : ↥(bar M Q (Rt M (LB M Q B) t))) = x :=
      Subtype.ext hn
    rw [MonoidHom.mem_ker, ← hx']
    refine Units.ext ?_
    change ((D.rho AM ⟨HS6.piM M Q n, hmem⟩ : GL (Fin 3) AM.K) :
      Matrix (Fin 3) (Fin 3) AM.K) = 1
    rw [D.rho_piM AM hnR hmem]
    exact rhoMat_eq_one_of_matV_eq_one D AM ⟨n, hnR⟩ (matV_eq_one_of_mem_CN D AM hnCN)

end Rho

end CFSG.RankThree.GF2n.Stroth80
