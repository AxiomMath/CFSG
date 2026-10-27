module

public import CFSG.RankThree.GF2n.Stroth80.Sec108FixA
public import CFSG.RankThree.GF2n.Stroth80.Sec108OddIndex

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

private theorem coeff_eq_of_id_add_smul_nu (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {c c' : AM.K}
    (h : (LinearMap.id + c • D.nu AM : AM.M₀.E →ₗ[AM.K] AM.M₀.E) =
      LinearMap.id + c' • D.nu AM) : c = c' := by
  refine D.eq_of_smul_nu AM fun e => ?_
  have hh := LinearMap.congr_fun h e
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply] at hh
  exact add_left_cancel hh

private theorem fix_range_commutator (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d r : G} (hd : d ∈ H0 M Z)
    (hr : r ∈ Rt M (LB M Q B) t) (hzH : ⁅r, d⁆ ∈ H0 M Z)
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨d, hd⟩ u = u) :
    ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨⁅r, d⁆, hzH⟩ u = u := by
  have hrH0 : r ∈ H0 M Z := D.Rt_le_H0 hr
  have hcommt : ∀ e, AM.φ (⟨r, hrH0⟩ : ↥(H0 M Z)) (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ (⟨r, hrH0⟩ : ↥(H0 M Z)) e) :=
    fun e => Sec108Data.phi_comm_of_comm_mem (m := (⟨r, hrH0⟩ : ↥(H0 M Z)))
      (m' := (⟨t, D.t_mem_H0⟩ : ↥(H0 M Z))) AM (hc.Rt_comm_mem_Q hr) e
  have hrInv : r⁻¹ ∈ Rt M (LB M Q B) t := Subgroup.inv_mem _ hr
  have hcommt_inv : ∀ e, AM.φ (⟨r⁻¹, D.Rt_le_H0 hrInv⟩ : ↥(H0 M Z))
      (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩
        (AM.φ (⟨r⁻¹, D.Rt_le_H0 hrInv⟩ : ↥(H0 M Z)) e) :=
    fun e => Sec108Data.phi_comm_of_comm_mem (m := (⟨r⁻¹, D.Rt_le_H0 hrInv⟩ : ↥(H0 M Z)))
      (m' := (⟨t, D.t_mem_H0⟩ : ↥(H0 M Z))) AM (hc.Rt_comm_mem_Q hrInv) e
  have hinv : (AM.φ (⟨r, hrH0⟩ : ↥(H0 M Z)))⁻¹ =
      AM.φ (⟨r⁻¹, D.Rt_le_H0 hrInv⟩ : ↥(H0 M Z)) := by
    rw [← map_inv]
    rfl
  intro u hu
  have hmem : AM.φ (⟨r⁻¹, D.Rt_le_H0 hrInv⟩ : ↥(H0 M Z)) u ∈
      Submodule.map (AM.φ (⟨r⁻¹, D.Rt_le_H0 hrInv⟩ : ↥(H0 M Z)) :
          AM.M₀.E →ₗ[AM.K] AM.M₀.E) (LinearMap.range (D.nu AM)) :=
    Submodule.mem_map_of_mem hu
  rw [D.map_range_nu AM hcommt_inv] at hmem
  have hmem' : (AM.φ (⟨r, hrH0⟩ : ↥(H0 M Z)))⁻¹ u ∈ LinearMap.range (D.nu AM) := by
    simpa [hinv] using hmem
  have hdU : (AM.φ (⟨d, hd⟩ : ↥(H0 M Z)))⁻¹ u = u := by
    calc (AM.φ (⟨d, hd⟩ : ↥(H0 M Z)))⁻¹ u
        = (AM.φ (⟨d, hd⟩ : ↥(H0 M Z)))⁻¹ (AM.φ (⟨d, hd⟩ : ↥(H0 M Z)) u) := by
          rw [hU u hu]
      _ = u := by
          simpa [LinearEquiv.coe_inv] using LinearEquiv.symm_apply_apply
            (e := (AM.φ (⟨d, hd⟩ : ↥(H0 M Z)) : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E)) u
  have hz : (⟨⁅r, d⁆, hzH⟩ : ↥(H0 M Z)) =
      (⟨r, hrH0⟩ : ↥(H0 M Z)) * ⟨d, hd⟩ * (⟨r, hrH0⟩ : ↥(H0 M Z))⁻¹ * ⟨d, hd⟩⁻¹ :=
    Subtype.ext rfl
  have hφ : AM.φ ⟨⁅r, d⁆, hzH⟩ = AM.φ (⟨r, hrH0⟩ : ↥(H0 M Z)) * AM.φ ⟨d, hd⟩ *
      (AM.φ (⟨r, hrH0⟩ : ↥(H0 M Z)))⁻¹ * (AM.φ ⟨d, hd⟩)⁻¹ := by
    rw [hz, map_mul, map_mul, map_mul, map_inv, map_inv]
  rw [hφ, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hdU,
    hU _ hmem']
  rw [← LinearEquiv.mul_apply]
  rw [mul_inv_cancel]
  rfl

private def commH0 (D : Sec108Data hc t Y) {d : G} (hd : d ∈ H0 M Z) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) : ↥(H0 M Z) :=
  ⁅(⟨r, D.Rt_le_H0 hr⟩ : ↥(H0 M Z)), ⟨d, hd⟩⁆

private theorem exists_commCoeff (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z)
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨d, hd⟩ u = u)
    (r : ↥(Rt M (LB M Q B) t)) :
    ∃ c : AM.K, (AM.φ (commH0 D hd r.2) : AM.M₀.E →ₗ[AM.K] AM.M₀.E) =
      LinearMap.id + c • D.nu AM := by
  have hCN : ⁅(r : G), d⁆ ∈ hc.CN t := D.comm_mem_CN_of_fix hd hdY hdV r.2
  have hfixU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ (commH0 D hd r.2) u = u :=
    fix_range_commutator D AM hd r.2 (commH0 D hd r.2).2 hU
  have hfixV : ∀ e ∈ AM.Vsp hc t, AM.φ (commH0 D hd r.2) e = e :=
    fun e he => hfixU e (D.Vsp_le_range_nu AM he)
  have ht : ∀ e, AM.φ (commH0 D hd r.2) (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ (commH0 D hd r.2) e) :=
    D.comm_t_of_mem_CN AM hCN
  have hS0 : D.phiMat AM (commH0 D hd r.2) = 0 :=
    (D.phiMat_eq_zero_iff AM hfixV ht).mpr hfixU
  obtain ⟨y, hy, hyq⟩ := (D.phiMat_eq_zero_iff_root AM hCN).mp hS0
  obtain ⟨c, hcφ⟩ := D.root_eq AM hy
  have hyH : y ∈ H0 M Z := hc.LB_le_H0 (D.root_le_LB hy)
  have hqH : y⁻¹ * ⁅(r : G), d⁆ ∈ H0 M Z :=
    (H0 M Z).mul_mem ((H0 M Z).inv_mem hyH) (commH0 D hd r.2).2
  have hsplit : commH0 D hd r.2 = (⟨y, hyH⟩ : ↥(H0 M Z)) *
      ⟨y⁻¹ * ⁅(r : G), d⁆, hqH⟩ := by
    apply Subtype.ext
    change ⁅(r : G), d⁆ = y * (y⁻¹ * ⁅(r : G), d⁆)
    group
  have hφq : AM.φ (⟨y⁻¹ * ⁅(r : G), d⁆, hqH⟩ : ↥(H0 M Z)) = 1 :=
    (AM.φ_ker _).mpr hyq
  have hEq : AM.φ (commH0 D hd r.2) = AM.φ (⟨y, hyH⟩ : ↥(H0 M Z)) := by
    rw [hsplit, map_mul, hφq, mul_one]
  refine ⟨c, ?_⟩
  rw [← hcφ]
  exact congrArg LinearEquiv.toLinearMap hEq

private theorem conj_add_smul_nu (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {A : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E}
    (hA : ∀ e, D.nu AM (A e) = A (D.nu AM e)) (c : AM.K) (y : AM.M₀.E) :
    A ((LinearMap.id + c • D.nu AM : AM.M₀.E →ₗ[AM.K] AM.M₀.E) (A.symm y)) =
      (LinearMap.id + c • D.nu AM : AM.M₀.E →ₗ[AM.K] AM.M₀.E) y := by
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, map_add, map_smul]
  rw [← hA (A.symm y), LinearEquiv.apply_symm_apply]

private noncomputable def fixCoeff (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z)
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨d, hd⟩ u = u)
    (r : ↥(Rt M (LB M Q B) t)) : AM.K :=
  (exists_commCoeff D AM hd hdY hdV hU r).choose

private theorem fixCoeff_spec (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z)
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨d, hd⟩ u = u)
    (r : ↥(Rt M (LB M Q B) t)) :
    (AM.φ (commH0 D hd r.2) : AM.M₀.E →ₗ[AM.K] AM.M₀.E) =
      LinearMap.id + fixCoeff D AM hd hdY hdV hU r • D.nu AM :=
  (exists_commCoeff D AM hd hdY hdV hU r).choose_spec

private theorem fixCoeff_conj_nu (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z)
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨d, hd⟩ u = u)
    (b : ↥(Rt M (LB M Q B) t)) {A : ↥(H0 M Z)}
    (hAnu : ∀ e, D.nu AM (AM.φ A e) = AM.φ A (D.nu AM e)) (y : AM.M₀.E) :
    AM.φ A (AM.φ (commH0 D hd b.2) ((AM.φ A).symm y)) =
      y + fixCoeff D AM hd hdY hdV hU b • D.nu AM y := by
  rw [show AM.φ (commH0 D hd b.2) ((AM.φ A).symm y) =
      (AM.φ A).symm y + fixCoeff D AM hd hdY hdV hU b • D.nu AM ((AM.φ A).symm y) from
    LinearMap.congr_fun (fixCoeff_spec D AM hd hdY hdV hU b) _]
  simpa using conj_add_smul_nu D AM hAnu (fixCoeff D AM hd hdY hdV hU b) y

private theorem fixCoeff_mul_spec (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z)
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨d, hd⟩ u = u)
    (a b : ↥(Rt M (LB M Q B) t)) :
    (AM.φ (commH0 D hd (a * b).2) : AM.M₀.E →ₗ[AM.K] AM.M₀.E) =
      LinearMap.id + (fixCoeff D AM hd hdY hdV hU a +
        fixCoeff D AM hd hdY hdV hU b) • D.nu AM := by
  have haH : (a : G) ∈ H0 M Z := D.Rt_le_H0 a.2
  have hbH : (b : G) ∈ H0 M Z := D.Rt_le_H0 b.2
  set A : ↥(H0 M Z) := ⟨(a : G), haH⟩
  have hcommt : ∀ e, AM.φ A (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ A e) :=
    fun e => Sec108Data.phi_comm_of_comm_mem (m := A)
      (m' := (⟨t, D.t_mem_H0⟩ : ↥(H0 M Z))) AM (hc.Rt_comm_mem_Q a.2) e
  have hAnu : ∀ e, D.nu AM (AM.φ A e) = AM.φ A (D.nu AM e) := D.nu_phi AM hcommt
  have hfa : ∀ x, AM.φ (commH0 D hd a.2) x =
      x + fixCoeff D AM hd hdY hdV hU a • D.nu AM x :=
    fun x => LinearMap.congr_fun (fixCoeff_spec D AM hd hdY hdV hU a) x
  have hH0 : commH0 D hd (a * b).2 =
      A * commH0 D hd b.2 * A⁻¹ * commH0 D hd a.2 := by
    apply Subtype.ext
    change ⁅(a : G) * (b : G), d⁆ =
      (a : G) * ⁅(b : G), d⁆ * (a : G)⁻¹ * ⁅(a : G), d⁆
    rw [commutatorElement_mul_left_eq_conj_mul]
  have hφ : (AM.φ (commH0 D hd (a * b).2) : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E) =
      AM.φ A * AM.φ (commH0 D hd b.2) * (AM.φ A)⁻¹ *
        AM.φ (commH0 D hd a.2) := by
    rw [hH0, map_mul, map_mul, map_mul, map_inv]
  ext e
  rw [hφ]
  change (AM.φ A * AM.φ (commH0 D hd b.2) * (AM.φ A)⁻¹ *
    AM.φ (commH0 D hd a.2) : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E) e =
    (LinearMap.id + (fixCoeff D AM hd hdY hdV hU a +
      fixCoeff D AM hd hdY hdV hU b) • D.nu AM : AM.M₀.E →ₗ[AM.K] AM.M₀.E) e
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [show (AM.φ A)⁻¹ (AM.φ (commH0 D hd a.2) e) =
    (AM.φ A).symm (AM.φ (commH0 D hd a.2) e) from rfl, hfa e]
  rw [fixCoeff_conj_nu D AM hd hdY hdV hU b hAnu]
  have h2 : D.nu AM (D.nu AM e) = 0 := LinearMap.congr_fun (D.nu_comp_nu AM) e
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, map_add, map_smul,
    h2, smul_zero, add_zero, add_smul]
  abel

private theorem fixCoeff_add (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z)
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨d, hd⟩ u = u)
    (a b : ↥(Rt M (LB M Q B) t)) :
    fixCoeff D AM hd hdY hdV hU (a * b) =
      fixCoeff D AM hd hdY hdV hU a + fixCoeff D AM hd hdY hdV hU b := by
  have hEq : (LinearMap.id + (fixCoeff D AM hd hdY hdV hU a +
        fixCoeff D AM hd hdY hdV hU b) • D.nu AM :
      AM.M₀.E →ₗ[AM.K] AM.M₀.E) =
      LinearMap.id + fixCoeff D AM hd hdY hdV hU (a * b) • D.nu AM := by
    rw [← fixCoeff_mul_spec D AM hd hdY hdV hU a b,
      fixCoeff_spec D AM hd hdY hdV hU (a * b)]
  exact (coeff_eq_of_id_add_smul_nu D AM hEq).symm

private theorem fixCoeff_one (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z)
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨d, hd⟩ u = u) :
    fixCoeff D AM hd hdY hdV hU 1 = 0 := by
  have h1 : (AM.φ (commH0 D hd (1 : ↥(Rt M (LB M Q B) t)).2) :
      AM.M₀.E →ₗ[AM.K] AM.M₀.E) = LinearMap.id := by
    have hH0 : commH0 D hd (1 : ↥(Rt M (LB M Q B) t)).2 = 1 := by
      apply Subtype.ext
      change ⁅(1 : G), d⁆ = 1
      simp [commutatorElement_def]
    rw [hH0, map_one]
    rfl
  have hEq : (LinearMap.id + (0 : AM.K) • D.nu AM : AM.M₀.E →ₗ[AM.K] AM.M₀.E) =
      LinearMap.id + fixCoeff D AM hd hdY hdV hU 1 • D.nu AM := by
    rw [zero_smul, add_zero, ← fixCoeff_spec D AM hd hdY hdV hU 1, h1]
  exact (coeff_eq_of_id_add_smul_nu D AM hEq).symm

private theorem fixCoeff_inv (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z)
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨d, hd⟩ u = u)
    (r : ↥(Rt M (LB M Q B) t)) :
    fixCoeff D AM hd hdY hdV hU r⁻¹ = - fixCoeff D AM hd hdY hdV hU r := by
  have h := fixCoeff_add D AM hd hdY hdV hU r r⁻¹
  rw [mul_inv_cancel, fixCoeff_one D AM hd hdY hdV hU] at h
  exact eq_neg_of_add_eq_zero_right h.symm

private theorem fixCoeff_commutator (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z)
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨d, hd⟩ u = u)
    (a b : ↥(Rt M (LB M Q B) t)) :
    fixCoeff D AM hd hdY hdV hU ⁅a, b⁆ = 0 := by
  rw [commutatorElement_def,
    fixCoeff_add D AM hd hdY hdV hU (a * b * a⁻¹) b⁻¹,
    fixCoeff_add D AM hd hdY hdV hU (a * b) a⁻¹,
    fixCoeff_add D AM hd hdY hdV hU a b,
    fixCoeff_inv D AM hd hdY hdV hU a, fixCoeff_inv D AM hd hdY hdV hU b]
  abel

private theorem fixCoeff_mem_Q (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z)
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨d, hd⟩ u = u)
    (q : G) (hq : q ∈ Q) :
    fixCoeff D AM hd hdY hdV hU ⟨q, hc.Q_le_Rt D.good.1.mem_LB hq⟩ = 0 := by
  have hcommQ : ⁅q, d⁆ ∈ Q := by
    rw [commutatorElement_def, show q * d * q⁻¹ * d⁻¹ = q * (d * q⁻¹ * d⁻¹) by group]
    exact Q.mul_mem hq ((hc.conj_mem_Q_of_mem_M hd.1).1 q⁻¹ (Q.inv_mem hq))
  have h1 : (AM.φ (commH0 D hd (hc.Q_le_Rt D.good.1.mem_LB hq)) :
      AM.M₀.E →ₗ[AM.K] AM.M₀.E) = LinearMap.id := by
    have hH0 : commH0 D hd (hc.Q_le_Rt D.good.1.mem_LB hq) =
        (⟨⁅q, d⁆, hc.Q_le_H0 hcommQ⟩ : ↥(H0 M Z)) := Subtype.ext rfl
    rw [hH0, (AM.φ_ker _).mpr hcommQ]
    rfl
  have hEq : (LinearMap.id + (0 : AM.K) • D.nu AM : AM.M₀.E →ₗ[AM.K] AM.M₀.E) =
      LinearMap.id + fixCoeff D AM hd hdY hdV hU ⟨q, hc.Q_le_Rt D.good.1.mem_LB hq⟩ •
        D.nu AM := by
    rw [zero_smul, add_zero, ← fixCoeff_spec D AM hd hdY hdV hU
      ⟨q, hc.Q_le_Rt D.good.1.mem_LB hq⟩, h1]
  exact (coeff_eq_of_id_add_smul_nu D AM hEq).symm

private theorem fixCoeff_mem_root (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z)
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨d, hd⟩ u = u)
    (hdt : ⁅d, t⁆ ∈ Q) (y : G) (hy : y ∈ Y) :
    fixCoeff D AM hd hdY hdV hU
      ⟨y, le_Rt (M := M) (LB M Q B) D.good.1.mem_LB (D.root_le_LB hy)⟩ = 0 := by
  have hyH : y ∈ H0 M Z := hc.LB_le_H0 (D.root_le_LB hy)
  obtain ⟨c, hcφ⟩ := D.root_eq AM hy
  have hdtc : ∀ e, AM.φ (⟨d, hd⟩ : ↥(H0 M Z)) (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ (⟨d, hd⟩ : ↥(H0 M Z)) e) :=
    fun e => Sec108Data.phi_comm_of_comm_mem (m := (⟨d, hd⟩ : ↥(H0 M Z)))
      (m' := (⟨t, D.t_mem_H0⟩ : ↥(H0 M Z))) AM hdt e
  have hdnu : ∀ e, D.nu AM (AM.φ (⟨d, hd⟩ : ↥(H0 M Z)) e) =
      AM.φ (⟨d, hd⟩ : ↥(H0 M Z)) (D.nu AM e) := D.nu_phi AM hdtc
  have hφy : ∀ x, AM.φ (⟨y, hyH⟩ : ↥(H0 M Z)) x = x + c • D.nu AM x :=
    fun x => LinearMap.congr_fun hcφ x
  have hcomm : AM.φ (⟨y, hyH⟩ : ↥(H0 M Z)) * AM.φ (⟨d, hd⟩ : ↥(H0 M Z)) =
      AM.φ (⟨d, hd⟩ : ↥(H0 M Z)) * AM.φ (⟨y, hyH⟩ : ↥(H0 M Z)) := by
    ext e
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hφy, hφy, map_add, map_smul, hdnu]
  have h1 : (AM.φ (commH0 D hd
      (le_Rt (M := M) (LB M Q B) D.good.1.mem_LB (D.root_le_LB hy))) :
      AM.M₀.E →ₗ[AM.K] AM.M₀.E) = LinearMap.id := by
    have hH0 : commH0 D hd
        (le_Rt (M := M) (LB M Q B) D.good.1.mem_LB (D.root_le_LB hy)) =
        ⁅(⟨y, hyH⟩ : ↥(H0 M Z)), (⟨d, hd⟩ : ↥(H0 M Z))⁆ := Subtype.ext rfl
    rw [hH0, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
    rfl
  have hEq : (LinearMap.id + (0 : AM.K) • D.nu AM : AM.M₀.E →ₗ[AM.K] AM.M₀.E) =
      LinearMap.id + fixCoeff D AM hd hdY hdV hU
        ⟨y, le_Rt (M := M) (LB M Q B) D.good.1.mem_LB (D.root_le_LB hy)⟩ • D.nu AM := by
    rw [zero_smul, add_zero, ← fixCoeff_spec D AM hd hdY hdV hU
      ⟨y, le_Rt (M := M) (LB M Q B) D.good.1.mem_LB (D.root_le_LB hy)⟩, h1]
  exact (coeff_eq_of_id_add_smul_nu D AM hEq).symm

private theorem commutator_Rt_le :
    ⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆ ≤ Rt M (LB M Q B) t := by
  rw [Subgroup.commutator_def]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨a, ha, b, hb, rfl⟩
  exact (Rt M (LB M Q B) t).mul_mem
    ((Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem ha hb)
      ((Rt M (LB M Q B) t).inv_mem ha)) ((Rt M (LB M Q B) t).inv_mem hb)

private theorem commutator_CN_le (hc : Ctx M Q Z B) :
    ⁅hc.CN t, Rt M (LB M Q B) t⁆ ≤ Rt M (LB M Q B) t := by
  rw [Subgroup.commutator_def]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨a, ha, b, hb, rfl⟩
  have haR : a ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp ha).1
  exact (Rt M (LB M Q B) t).mul_mem
    ((Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem haR hb)
      ((Rt M (LB M Q B) t).inv_mem haR)) ((Rt M (LB M Q B) t).inv_mem hb)

private theorem fixCoeff_commutator_subgroup (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z)
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨d, hd⟩ u = u) :
    ∀ (x : G) (hx : x ∈ Rt M (LB M Q B) t),
      x ∈ ⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆ →
      fixCoeff D AM hd hdY hdV hU ⟨x, hx⟩ = 0 := by
  let R : Subgroup G := Rt M (LB M Q B) t
  let Kf : Subgroup G :=
    { carrier := {x | ∃ hx : x ∈ R, fixCoeff D AM hd hdY hdV hU ⟨x, hx⟩ = 0}
      one_mem' := ⟨R.one_mem, fixCoeff_one D AM hd hdY hdV hU⟩
      mul_mem' := by
        rintro x y ⟨hx, hfx⟩ ⟨hy, hfy⟩
        refine ⟨R.mul_mem hx hy, ?_⟩
        have h := fixCoeff_add D AM hd hdY hdV hU ⟨x, hx⟩ ⟨y, hy⟩
        rw [hfx, hfy, add_zero] at h
        exact h
      inv_mem' := by
        rintro x ⟨hx, hfx⟩
        refine ⟨R.inv_mem hx, ?_⟩
        rw [show (⟨x⁻¹, R.inv_mem hx⟩ : ↥R) = (⟨x, hx⟩ : ↥R)⁻¹ from Subtype.ext rfl,
          fixCoeff_inv D AM hd hdY hdV hU ⟨x, hx⟩, hfx, neg_zero] }
  have hcommle : ⁅R, R⁆ ≤ Kf := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb), ?_⟩
    have h := fixCoeff_commutator D AM hd hdY hdV hU ⟨a, ha⟩ ⟨b, hb⟩
    rw [show (⟨⁅a, b⁆, R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha))
      (R.inv_mem hb)⟩ : ↥R) = ⁅(⟨a, ha⟩ : ↥R), (⟨b, hb⟩ : ↥R)⁆ from Subtype.ext rfl]
    exact h
  intro x hx hxcomm
  obtain ⟨hx', hfx⟩ := hcommle hxcomm
  exact hfx

private theorem fixCoeff_mem_CN (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z)
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨d, hd⟩ u = u)
    (hdt : ⁅d, t⁆ ∈ Q) (n : G) (hn : n ∈ hc.CN t) :
    fixCoeff D AM hd hdY hdV hU ⟨n, (Ctx.mem_CN.mp hn).1⟩ = 0 := by
  obtain ⟨c, hcComm, y, hy, hyq⟩ := D.exists_commutator_root hn
  have hcR : c ∈ Rt M (LB M Q B) t := commutator_CN_le hc hcComm
  have hyR : y ∈ Rt M (LB M Q B) t :=
    le_Rt (M := M) (LB M Q B) D.good.1.mem_LB (D.root_le_LB hy)
  have hqR : (c * y)⁻¹ * n ∈ Rt M (LB M Q B) t :=
    (Rt M (LB M Q B) t).mul_mem
      ((Rt M (LB M Q B) t).inv_mem ((Rt M (LB M Q B) t).mul_mem hcR hyR))
      (Ctx.mem_CN.mp hn).1
  have hcCommR : c ∈ ⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆ :=
    (Subgroup.commutator_mono (fun x hx => (Ctx.mem_CN.mp hx).1) le_rfl) hcComm
  have hcalc : fixCoeff D AM hd hdY hdV hU ⟨n, (Ctx.mem_CN.mp hn).1⟩ =
      fixCoeff D AM hd hdY hdV hU ⟨c, hcR⟩ + fixCoeff D AM hd hdY hdV hU ⟨y, hyR⟩ +
        fixCoeff D AM hd hdY hdV hU ⟨(c * y)⁻¹ * n, hqR⟩ := by
    rw [show (⟨n, (Ctx.mem_CN.mp hn).1⟩ : ↥(Rt M (LB M Q B) t)) =
        ⟨c, hcR⟩ * ⟨y, hyR⟩ * ⟨(c * y)⁻¹ * n, hqR⟩ from
      Subtype.ext (by change n = c * y * ((c * y)⁻¹ * n); group)]
    rw [fixCoeff_add D AM hd hdY hdV hU (⟨c, hcR⟩ * ⟨y, hyR⟩)
      ⟨(c * y)⁻¹ * n, hqR⟩,
      fixCoeff_add D AM hd hdY hdV hU ⟨c, hcR⟩ ⟨y, hyR⟩]
  rw [hcalc, fixCoeff_commutator_subgroup D AM hd hdY hdV hU c hcR hcCommR,
    fixCoeff_mem_root D AM hd hdY hdV hU hdt y hy,
    fixCoeff_mem_Q D AM hd hdY hdV hU ((c * y)⁻¹ * n) hyq]
  simp

private theorem fixCoeff_mem_Rt (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z)
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨d, hd⟩ u = u)
    (hdt : ⁅d, t⁆ ∈ Q) :
    ∀ (r : G) (hr : r ∈ Rt M (LB M Q B) t),
      fixCoeff D AM hd hdY hdV hU ⟨r, hr⟩ = 0 := by
  intro r hr
  obtain ⟨c, hcComm, hn⟩ := D.exists_commutator_mul_CN hr
  have hcR : c ∈ Rt M (LB M Q B) t := commutator_Rt_le hcComm
  have hnR : c⁻¹ * r ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hn).1
  have hcalc : fixCoeff D AM hd hdY hdV hU ⟨r, hr⟩ =
      fixCoeff D AM hd hdY hdV hU ⟨c, hcR⟩ +
        fixCoeff D AM hd hdY hdV hU ⟨c⁻¹ * r, hnR⟩ := by
    rw [show (⟨r, hr⟩ : ↥(Rt M (LB M Q B) t)) = ⟨c, hcR⟩ * ⟨c⁻¹ * r, hnR⟩ from
      Subtype.ext (by change r = c * (c⁻¹ * r); group)]
    exact fixCoeff_add D AM hd hdY hdV hU ⟨c, hcR⟩ ⟨c⁻¹ * r, hnR⟩
  rw [hcalc, fixCoeff_commutator_subgroup D AM hd hdY hdV hU c hcR hcComm,
    fixCoeff_mem_CN D AM hd hdY hdV hU hdt (c⁻¹ * r) hn]
  simp

private theorem comm_Rt_of_fix_range (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdt : ⁅d, t⁆ ∈ Q)
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨d, hd⟩ u = u) :
    ∀ r ∈ Rt M (LB M Q B) t, ⁅r, d⁆ ∈ Q := by
  have hV : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨d, hd⟩ e = e :=
    fun e he => hU e (D.Vsp_le_range_nu AM he)
  have hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z :=
    hc.comm_Vt_of_fix AM hd hV
  intro r hr
  have hfr : fixCoeff D AM hd hdY hdV hU ⟨r, hr⟩ = 0 :=
    fixCoeff_mem_Rt D AM hd hdY hdV hU hdt r hr
  have h1 : (AM.φ (commH0 D hd hr) : AM.M₀.E →ₗ[AM.K] AM.M₀.E) = LinearMap.id := by
    rw [fixCoeff_spec D AM hd hdY hdV hU ⟨r, hr⟩, hfr, zero_smul, add_zero]
  have h2 : AM.φ (commH0 D hd hr) = 1 := by
    rw [← LinearEquiv.toLinearMap_inj]
    rw [h1]
    rfl
  exact (AM.φ_ker (commH0 D hd hr)).mp h2

theorem Sec108Data.exists_root_of_fix_U (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)) (hdt : ⁅d, t⁆ ∈ Q)
    (hU : ∀ u ∈ LinearMap.range (D.nu AM), AM.φ ⟨d, hd⟩ u = u) : ∃ y ∈ Y, y⁻¹ * d ∈ Q := by
  have hcomm : ∀ m' : ↥(H0 M Z), (m' : G) ∈ Rt M (LB M Q B) t →
      (∀ e, AM.φ m' (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m' e)) →
      ∀ e, AM.φ ⟨d, hd⟩ (AM.φ m' e) = AM.φ m' (AM.φ ⟨d, hd⟩ e) := by
    intro m' hm' _
    have hq : ⁅(d : G), (m' : G)⁆ ∈ Q := by
      rw [← commutatorElement_inv]
      exact Q.inv_mem (comm_Rt_of_fix_range D AM hd hdY hdt hU (m' : G) hm')
    exact Sec108Data.phi_comm_of_comm_mem (m := (⟨d, hd⟩ : ↥(H0 M Z))) (m' := m') AM hq
  obtain ⟨c, hcφ⟩ := D.eq_id_add_smul_nu AM ⟨d, hd⟩ hcomm hU
  obtain ⟨y, hy, hyc⟩ := D.exists_root_eq_smul AM c
  refine ⟨y, hy, ?_⟩
  have hyH : y ∈ H0 M Z := hc.LB_le_H0 (D.root_le_LB hy)
  have heq : AM.φ (⟨d, hd⟩ : ↥(H0 M Z)) = AM.φ (⟨y, hyH⟩ : ↥(H0 M Z)) :=
    LinearEquiv.toLinearMap_injective (by rw [hcφ, hyc])
  have hH0 : y⁻¹ * d ∈ H0 M Z := (H0 M Z).mul_mem ((H0 M Z).inv_mem hyH) hd
  have h1 : AM.φ ((⟨y, hyH⟩ : ↥(H0 M Z))⁻¹ * ⟨d, hd⟩) = 1 := by
    rw [map_mul, map_inv, heq, inv_mul_cancel]
  have hmem : (⟨y, hyH⟩ : ↥(H0 M Z))⁻¹ * ⟨d, hd⟩ = ⟨y⁻¹ * d, hH0⟩ := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  rw [hmem] at h1
  exact (AM.φ_ker _).mp h1

theorem Sec108Data.mem_CN_of_fix (D : Sec108Data hc t Y) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    (hdV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅d, v⁆ ∈ Z) (hdt : ⁅d, t⁆ ∈ Q) : d ∈ hc.CN t := by
  obtain ⟨AM⟩ := Smith81.Smith23E1.ActionModel.nonempty hc.hyp
  obtain ⟨n, hn, h1, hU⟩ := D.exists_CN_fix_U AM hd hdY hdV hdt
  have hnR : n ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hn).1
  have hnN : n ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) :=
    D.Rt_le_normalizer_root hnR
  have hd'Y : n⁻¹ * d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hnN) hdY
  have hnInvR : n⁻¹ ∈ Rt M (LB M Q B) t := Subgroup.inv_mem _ hnR
  have hd't : ⁅n⁻¹ * d, t⁆ ∈ Q := by
    rw [commutatorElement_mul_left_eq_conj_mul]
    refine Q.mul_mem ?_ (hc.Rt_comm_mem_Q hnInvR)
    exact (hc.conj_mem_Q_of_mem_M (M.inv_mem (hc.Rt_le_M t hnR))).1 ⁅d, t⁆ hdt
  obtain ⟨y, hy, hyq⟩ := D.exists_root_of_fix_U AM h1 hd'Y hd't hU
  have hY_CN : Y ≤ hc.CN t := by
    intro x hx
    have hxM : x ∈ M := ((smith_1_12 D.sit).1 hx).1
    have hxQB : x ∈ QB Y := by
      obtain ⟨g, hgY, hgQB, -⟩ := D.sit.QB_eq
      rw [hgQB]
      rw [hgY] at hx
      exact Subgroup.map_mono hc.hyp.Z_normal.1 hx
    rw [D.CN_eq]
    exact Subgroup.mem_sup_right ⟨hxQB, hxM⟩
  have hQ_CN : Q ≤ hc.CN t := hc.Q_le_CN D.good.1.mem_LB
  have hyCN : y ∈ hc.CN t := hY_CN hy
  have hqCN : y⁻¹ * (n⁻¹ * d) ∈ hc.CN t := hQ_CN hyq
  have hd_eq : d = n * (y * (y⁻¹ * (n⁻¹ * d))) := by group
  rw [hd_eq]
  exact (hc.CN t).mul_mem hn ((hc.CN t).mul_mem hyCN hqCN)

private theorem phi_inv_phi (AM : Smith81.Smith23E1.ActionModel M Q Z) (r : ↥(H0 M Z))
    (x : AM.M₀.E) : AM.φ r⁻¹ (AM.φ r x) = x := by
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

private theorem nuMul_eq_one_iff (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (d : ↥(H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) :
    D.nuMul AM d = 1 ↔ ⁅(d : G), t⁆ ∈ Q := by
  have hcomm : ⁅(d : G), t⁆ ∈ Q ↔ ∀ e, AM.φ ⟨d, d.2.1⟩ (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨d, d.2.1⟩ e) := by
    rw [show ⁅(d : G), t⁆ = ((⁅(⟨d, d.2.1⟩ : ↥(H0 M Z)), ⟨t, D.t_mem_H0⟩⁆ : ↥(H0 M Z)) : G) from
      rfl, ← AM.φ_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact ⟨fun h e => by simpa only [LinearEquiv.mul_apply] using LinearEquiv.congr_fun h e,
      fun h => LinearEquiv.ext fun e => by simpa only [LinearEquiv.mul_apply] using h e⟩
  rw [hcomm]
  constructor
  · intro h1 e
    have h := D.nuMul_spec AM d e
    rw [h1, Units.val_one, one_smul] at h
    rw [D.nu_apply AM e, D.nu_apply AM, map_sub] at h
    rw [show AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨d, d.2.1⟩ e) =
      (AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨d, d.2.1⟩ e) - AM.φ ⟨d, d.2.1⟩ e) + AM.φ ⟨d, d.2.1⟩ e by abel,
      ← h]
    abel
  · intro h
    refine Units.ext (D.eq_of_smul_nu AM fun x => ?_)
    obtain ⟨e, rfl⟩ := (AM.φ ⟨d, d.2.1⟩).surjective x
    rw [← D.nuMul_spec, ← D.nu_phi AM h, Units.val_one, one_smul]

private theorem fix_of_eq_inv_mul (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {r : G} (hrH : r ∈ H0 M Z)
    (d d' : ↥(H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)))
    (hd' : (d' : G) = r⁻¹ * d)
    (hr : ∀ j, AM.φ ⟨r, hrH⟩ (D.bV AM j) =
      ∑ i, D.matV AM ⟨d, d.2.1⟩ i j • (D.bV AM i : AM.M₀.E)) :
    ∀ e ∈ AM.Vsp hc t, AM.φ ⟨d', d'.2.1⟩ e = e := by
  have hφ : ∀ x, AM.φ ⟨d', d'.2.1⟩ x = AM.φ (⟨r, hrH⟩ : ↥(H0 M Z))⁻¹ (AM.φ ⟨d, d.2.1⟩ x) := by
    intro x
    rw [← LinearEquiv.mul_apply, ← map_mul]
    congr 2
    exact Subtype.ext hd'
  have hfixb : ∀ j, AM.φ ⟨d', d'.2.1⟩ (D.bV AM j) =
      ∑ i, (1 : Matrix (Fin 3) (Fin 3) AM.K) i j • (D.bV AM i : AM.M₀.E) := by
    intro j
    rw [hφ, D.phi_bV_eq_sum AM (fun e he => D.phi_mem_Vsp_of_normalizer AM d.2.1 d.2.2 he) j,
      ← hr j, phi_inv_phi]
    simp [Matrix.one_apply]
  exact (D.matV_eq_one_iff AM fun e he => D.phi_mem_Vsp_of_normalizer AM d'.2.1 d'.2.2 he).mp
    (D.matV_eq_of_forall AM hfixb)

theorem Sec108Data.ker_oddChar_le (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    (D.oddChar AM).ker ≤ (Rt M (LB M Q B) t).subgroupOf
      (H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)) := by
  intro d hd
  rw [MonoidHom.mem_ker] at hd
  rw [Subgroup.mem_subgroupOf]
  have h1 : (D.matV AM ⟨d, d.2.1⟩).det = 1 := by rw [← D.oddChar_fst, hd]; rfl
  obtain ⟨r, ⟨hrR, hrt⟩, hrH, hr⟩ := D.bV_spec AM ⟨D.matV AM ⟨d, d.2.1⟩, h1⟩
  have hrD : r ∈ H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) :=
    ⟨hrH, D.Rt_le_normalizer_root hrR⟩
  set d' := (⟨r, hrD⟩ : ↥(H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)))⁻¹ * d
  have hfix := fix_of_eq_inv_mul D AM hrH d d' rfl hr
  have hrc : D.nuMul AM ⟨r, hrD⟩ = 1 := (nuMul_eq_one_iff D AM _).mpr (by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_singleton_iff.mp hrt)]
    exact Q.one_mem)
  have hd'c : D.nuMul AM d' = 1 := by
    have h := congrArg Prod.snd (map_mul (D.oddChar AM) ⟨r, hrD⟩ d')
    rw [mul_inv_cancel_left] at h
    rw [Prod.snd_mul, D.oddChar_snd_eq, D.oddChar_snd_eq, D.oddChar_snd_eq] at h
    rw [show D.nuMul AM d = 1 by rw [← D.oddChar_snd_eq, hd, Prod.snd_one], hrc, one_mul] at h
    exact h.symm
  have hd'N := D.mem_CN_of_fix d'.2.1 d'.2.2 (hc.comm_Vt_of_fix AM d'.2.1 hfix)
    ((nuMul_eq_one_iff D AM d').mp hd'c)
  have hdeq : (d : G) = r * (d' : G) := by
    simp only [d', Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [hdeq]
  exact (Rt M (LB M Q B) t).mul_mem hrR (Ctx.mem_CN.mp hd'N).1

theorem Sec108Data.twoElt_mem_Rt (D : Sec108Data hc t Y) {d : G} (hd : d ∈ H0 M Z)
    (hdY : d ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)) {k : ℕ} (h2 : d ^ 2 ^ k ∈ Q) :
    d ∈ Rt M (LB M Q B) t := by
  obtain ⟨AM⟩ := Smith81.Smith23E1.ActionModel.nonempty hc.hyp
  set d' : ↥(H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)) := ⟨d, hd, hdY⟩
  have h1 : D.oddChar AM d' ^ 2 ^ k = 1 := by
    rw [← map_pow]
    exact D.oddChar_eq_one_of_mem_Q AM _ (by rw [Subgroup.coe_pow]; exact h2)
  have hord : orderOf (D.oddChar AM d') = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k
      (Nat.coprime_two_left.mpr (D.odd_card_units_prod AM)))
      (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_natCard _)
  have hker : d' ∈ (D.oddChar AM).ker := MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp hord)
  exact Subgroup.mem_subgroupOf.mp (D.ker_oddChar_le AM hker)

end CFSG.RankThree.GF2n.Stroth80
