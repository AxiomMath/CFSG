module

public import CFSG.RankThree.GF2n.Stroth80.Sec108Rho
public import CFSG.RankThree.GF2n.Stroth80.Sec108NormCN

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

private theorem piM_mem_bar_root_of_mem_sup [(Q.subgroupOf M).Normal]
    (D : Sec108Data hc t Y) {z : G} (hz : z ∈ Y ⊔ Q) :
    HS6.piM M Q z ∈ bar M Q Y := by
  obtain ⟨y, hy, w, hw, rfl⟩ := D.exists_root_mul hz
  have hyM : y ∈ M := hc.LB_le_M (D.root_le_LB hy)
  have hwM : w ∈ M := hc.hyp.Q_normal.1 hw
  rw [HS6.piM_mul hyM hwM, (HS6.piM_eq_one_iff hwM).mpr hw, mul_one]
  exact HS6.piM_mem_bar hy hyM

private theorem piM_mem_normalizer_bar_root_iff [(Q.subgroupOf M).Normal]
    (D : Sec108Data hc t Y) {g : G} (hgM : g ∈ M) :
    HS6.piM M Q g ∈ Subgroup.normalizer (bar M Q Y : Set (Mbar M Q)) ↔
      g ∈ Subgroup.normalizer (((Y ⊔ Q : Subgroup G)) : Set G) := by
  constructor
  · intro hx
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    have hzM : z ∈ M :=
      (sup_le (fun y hy => hc.LB_le_M (D.root_le_LB hy)) hc.hyp.Q_normal.1) hz
    have hzbar : HS6.piM M Q z ∈ bar M Q Y := piM_mem_bar_root_of_mem_sup D hz
    have h1 : HS6.piM M Q (g * z * g⁻¹) ∈ bar M Q Y := by
      rw [HS6.piM_conj hgM hzM]
      exact (Subgroup.mem_normalizer_iff.mp hx _).mp hzbar
    exact (HS6.piM_mem_bar_iff (le_sup_right : Q ≤ Y ⊔ Q)
      (M.mul_mem (M.mul_mem hgM hzM) (M.inv_mem hgM))).mp
      (HS6.bar_mono (le_sup_left : Y ≤ Y ⊔ Q) h1)
  · intro hgYQ
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨y, hy, hyM, rfl⟩ := (HS6.mem_bar z).mp hz
    have hgy : g * y * g⁻¹ ∈ Y ⊔ Q :=
      (Subgroup.mem_normalizer_iff.mp hgYQ y).mp (Subgroup.mem_sup_left hy)
    have h1 : HS6.piM M Q (g * y * g⁻¹) ∈ bar M Q Y :=
      piM_mem_bar_root_of_mem_sup D hgy
    rw [← HS6.piM_mul hgM hyM, ← HS6.piM_inv hgM,
      ← HS6.piM_mul (M.mul_mem hgM hyM) (M.inv_mem hgM)]
    exact h1

theorem Sec108Data.normalizer_bar_root_le [(Q.subgroupOf M).Normal] (D : Sec108Data hc t Y) :
    Subgroup.normalizer (bar M Q Y : Set (Mbar M Q)) ≤
      Subgroup.normalizer (bar M Q (Rt M (LB M Q B) t) : Set (Mbar M Q)) := by
  intro x hx
  obtain ⟨g, hgM, rfl⟩ := HS6.exists_piM x
  have hgYQ := (piM_mem_normalizer_bar_root_iff D hgM).mp hx
  have hgRt : g ∈ Subgroup.normalizer (Rt M (LB M Q B) t : Set G) :=
    (D.mem_normalizer_root_iff_Rt hgM).mp hgYQ
  exact HS6.piM_mem_normalizer hc.hyp.Q_normal.1 hgM (conjSubgroup_eq_self_iff.mpr hgRt)

theorem Sec108Data.normalizer_bar_inf_le [(Q.subgroupOf M).Normal] (D : Sec108Data hc t Y) :
    Subgroup.normalizer ((bar M Q (LB M Q B) ⊓ bar M Q (hc.CN t) : Subgroup (Mbar M Q)) :
      Set (Mbar M Q)) ≤ Subgroup.normalizer (bar M Q Y : Set (Mbar M Q)) := by
  intro x hx
  obtain ⟨g, hgM, rfl⟩ := HS6.exists_piM x
  have hQK : Q ≤ LB M Q B ⊓ hc.CN t :=
    le_inf sec39_Q_le_LB (hc.Q_le_CN D.good.1.mem_LB)
  have hKM : LB M Q B ⊓ hc.CN t ≤ M := inf_le_left.trans hc.LB_le_M
  have hx' : HS6.piM M Q g ∈
      Subgroup.normalizer (bar M Q (LB M Q B ⊓ hc.CN t) : Set (Mbar M Q)) := by
    rw [HS6.bar_inf sec39_Q_le_LB (hc.Q_le_CN D.good.1.mem_LB)]
    exact hx
  rw [HS6.piM_of_mem hgM] at hx'
  have hgK : g ∈ Subgroup.normalizer ((LB M Q B ⊓ hc.CN t : Subgroup G) : Set G) :=
    mem_normalizer_of_mk_mem_normalizer_bar hQK hKM ⟨g, hgM⟩ hx'
  have hgV : g ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    have hvQ : v ∈ Q := hc.Vt_le_Q t hv
    have hgvQ : g * v * g⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgM) v).mp hvQ
    refine D.mem_Vt_of_comm hgvQ fun n hn => ?_
    have hgn : g⁻¹ * n * g ∈ LB M Q B ⊓ hc.CN t :=
      (Subgroup.mem_normalizer_iff''.mp hgK n).mp hn
    have hz : ⁅g⁻¹ * n * g, v⁆ ∈ Z :=
      (Ctx.mem_CN.mp (Subgroup.mem_inf.mp hgn).2).2 v hv
    have hconj : ⁅n, g * v * g⁻¹⁆ = g * ⁅g⁻¹ * n * g, v⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hconj]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hgM) _).mp hz
  exact (piM_mem_normalizer_bar_root_iff D hgM).mpr
    ((D.mem_normalizer_root_iff_Vt hgM).mpr hgV)

section Mu

variable (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)

noncomputable def Sec108Data.muVec (n : ↥(hc.CN t)) : Fin 3 → AM.K :=
  (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)ᵀ *ᵥ
    ![D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ 2 1, D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ 0 2,
      D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ 1 0]

private theorem Sec108Data.muVec_add (n n' : ↥(hc.CN t)) :
    D.muVec AM (n * n') = D.muVec AM n + D.muVec AM n' := by
  have hmat : D.phiMat AM ⟨n * n', D.CN_le_H0 (n * n').2⟩ =
      D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ + D.phiMat AM ⟨n', D.CN_le_H0 n'.2⟩ :=
    D.phiMat_mul AM (m := ⟨n, D.CN_le_H0 n.2⟩) (m' := ⟨n', D.CN_le_H0 n'.2⟩)
      (fun e he => D.fix_Vsp_of_mem_CN AM n.2 he)
      (fun e he => D.fix_Vsp_of_mem_CN AM n'.2 he) (D.comm_t_of_mem_CN AM n'.2)
  have hvec : ![D.phiMat AM ⟨↑(n * n'), D.CN_le_H0 (n * n').2⟩ 2 1,
        D.phiMat AM ⟨↑(n * n'), D.CN_le_H0 (n * n').2⟩ 0 2,
        D.phiMat AM ⟨↑(n * n'), D.CN_le_H0 (n * n').2⟩ 1 0] =
      ![D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ 2 1,
          D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ 0 2,
          D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ 1 0] +
        ![D.phiMat AM ⟨n', D.CN_le_H0 n'.2⟩ 2 1,
          D.phiMat AM ⟨n', D.CN_le_H0 n'.2⟩ 0 2,
          D.phiMat AM ⟨n', D.CN_le_H0 n'.2⟩ 1 0] := by
    funext i
    fin_cases i <;> simp [hmat]
  simp only [Sec108Data.muVec, hvec, Matrix.mulVec_add]

theorem Sec108Data.muVec_mul (n n' : ↥(hc.CN t)) :
    Multiplicative.ofAdd (D.muVec AM (n * n')) =
      Multiplicative.ofAdd (D.muVec AM n) * Multiplicative.ofAdd (D.muVec AM n') := by
  rw [D.muVec_add AM]
  rfl

noncomputable def Sec108Data.mu₀ : ↥(hc.CN t) →* Multiplicative (Fin 3 → AM.K) :=
  MonoidHom.mk' (fun n => Multiplicative.ofAdd (D.muVec AM n)) (D.muVec_mul AM)

theorem Sec108Data.mu₀_eq_one (n : ↥(hc.CN t)) (hn : (n : G) ∈ Q) : D.mu₀ AM n = 1 := by
  have hzero : D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ = 0 :=
    (D.phiMat_eq_zero_iff_root AM n.2).mpr
      ⟨1, Y.one_mem, by simpa using hn⟩
  apply Multiplicative.toAdd.injective
  show D.muVec AM n = Multiplicative.toAdd (1 : Multiplicative (Fin 3 → AM.K))
  rw [show Multiplicative.toAdd (1 : Multiplicative (Fin 3 → AM.K)) = 0 from rfl]
  simp only [Sec108Data.muVec, hzero]
  exact Matrix.mulVec_zero ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)ᵀ)

variable [(Q.subgroupOf M).Normal]

noncomputable def Sec108Data.mu : ↥(bar M Q (hc.CN t)) →* Multiplicative (Fin 3 → AM.K) :=
  barLift (D.mu₀ AM) (D.mu₀_eq_one AM)

theorem Sec108Data.mu_piM {n : G} (hn : n ∈ hc.CN t) (h : HS6.piM M Q n ∈ bar M Q (hc.CN t)) :
    Multiplicative.toAdd (D.mu AM ⟨HS6.piM M Q n, h⟩) = D.muVec AM ⟨n, hn⟩ := by
  have hnM : n ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hn).1
  have h1 := barLift_piM (D.mu₀ AM) (D.mu₀_eq_one AM) (⟨n, hn⟩ : ↥(hc.CN t)) hnM h
  change Multiplicative.toAdd ((barLift (D.mu₀ AM) (D.mu₀_eq_one AM))
    ⟨HS6.piM M Q n, h⟩) = D.muVec AM ⟨n, hn⟩
  rw [h1]
  rfl

private theorem crossMatrix_axis {K : Type} [Field K] (a : Fin 3 → K) :
    ![CFSG.LinearAlgebra.crossMatrix a 2 1, CFSG.LinearAlgebra.crossMatrix a 0 2,
      CFSG.LinearAlgebra.crossMatrix a 1 0] = a := by
  ext i
  fin_cases i <;> simp [CFSG.LinearAlgebra.crossMatrix]

private theorem crossMatrix_transpose_self {K : Type} [Field K] [CharP K 2]
    (a : Fin 3 → K) :
    (CFSG.LinearAlgebra.crossMatrix a)ᵀ = CFSG.LinearAlgebra.crossMatrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.LinearAlgebra.crossMatrix, CharTwo.neg_eq]

private theorem crossMatrix_diag {K : Type} [Field K] (a : Fin 3 → K) :
    ∀ i, CFSG.LinearAlgebra.crossMatrix a i i = 0 := by
  intro i
  fin_cases i <;> simp [CFSG.LinearAlgebra.crossMatrix]

private theorem Sec108Data.muVec_eq_zero_iff_phiMat (n : ↥(hc.CN t)) :
    D.muVec AM n = 0 ↔ D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ = 0 := by
  constructor
  · intro h
    have hPdet : (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K).det = 1 := (D.frameB AM).2
    have hPt : ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)ᵀ).det = 1 := by
      rw [Matrix.det_transpose, hPdet]
    have haxis : ![D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ 2 1,
        D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ 0 2,
        D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ 1 0] = 0 := by
      have := congrArg (fun v : Fin 3 → AM.K =>
        ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)ᵀ)⁻¹ *ᵥ v) h
      simpa only [Sec108Data.muVec, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (by rw [hPt]; exact isUnit_one),
        Matrix.one_mulVec, Matrix.mulVec_zero] using this
    have hsym : (D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩)ᵀ =
        D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ :=
      D.phiMat_transpose AM (fun e he => D.fix_Vsp_of_mem_CN AM n.2 he)
        (D.comm_t_of_mem_CN AM n.2)
    have hcross : D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ =
        CFSG.LinearAlgebra.crossMatrix ![D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ 2 1,
          D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ 0 2,
          D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ 1 0] := by
      refine CFSG.LinearAlgebra.eq_crossMatrix ?_ (fun i => D.phiMat_diag AM n.2 i)
      simpa [CharTwo.neg_eq] using hsym
    rw [hcross, haxis]
    exact (CFSG.LinearAlgebra.crossMatrix_eq_zero_iff 0).mpr rfl
  · intro h
    rw [Sec108Data.muVec, h]
    simp only [Matrix.zero_apply]
    exact Matrix.mulVec_zero ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)ᵀ)

theorem Sec108Data.surjective_mu : Function.Surjective (D.mu AM) := by
  intro y
  set P : Matrix (Fin 3) (Fin 3) AM.K := (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) with hP
  set a : Fin 3 → AM.K := (Pᵀ)⁻¹ *ᵥ Multiplicative.toAdd y with ha
  have hPdet : P.det = 1 := (D.frameB AM).2
  have hsym : (CFSG.LinearAlgebra.crossMatrix a)ᵀ = CFSG.LinearAlgebra.crossMatrix a :=
    crossMatrix_transpose_self a
  obtain ⟨n, hn, hSn⟩ := D.exists_phiMat_eq AM (CFSG.LinearAlgebra.crossMatrix a) hsym
    (crossMatrix_diag a)
  have hnM : n ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hn).1
  refine ⟨⟨HS6.piM M Q n, HS6.piM_mem_bar hn hnM⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [D.mu_piM AM hn (HS6.piM_mem_bar hn hnM)]
  rw [show D.muVec AM ⟨n, hn⟩ = Pᵀ *ᵥ
      ![D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 2 1,
        D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 0 2,
        D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 1 0] from rfl]
  rw [hSn, crossMatrix_axis]
  have hPt : (Pᵀ).det = 1 := by rw [Matrix.det_transpose, hPdet]
  rw [ha, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (by rw [hPt]; exact isUnit_one), Matrix.one_mulVec]

theorem Sec108Data.ker_mu : (D.mu AM).ker = (bar M Q Y).subgroupOf (bar M Q (hc.CN t)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    obtain ⟨n, hnCN, hnM, hxeq⟩ := (HS6.mem_bar (S := hc.CN t) (x : Mbar M Q)).mp x.2
    have hxsub : (⟨HS6.piM M Q n, HS6.piM_mem_bar hnCN hnM⟩ :
        ↥(bar M Q (hc.CN t))) = x := Subtype.ext hxeq
    rw [← hxsub] at hx
    rw [← hxeq]
    have hmu : Multiplicative.toAdd (D.mu AM ⟨HS6.piM M Q n,
        HS6.piM_mem_bar hnCN hnM⟩) = 0 := by
      rw [hx]
      rfl
    rw [D.mu_piM AM hnCN] at hmu
    have hzero : D.phiMat AM ⟨n, D.CN_le_H0 hnCN⟩ = 0 :=
      (D.muVec_eq_zero_iff_phiMat AM ⟨n, hnCN⟩).mp hmu
    obtain ⟨y, hy, hyq⟩ := (D.phiMat_eq_zero_iff_root AM hnCN).mp hzero
    have hyM : y ∈ M := hc.LB_le_M (D.root_le_LB hy)
    have hnM' : n ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hnCN).1
    have hpi : HS6.piM M Q n = HS6.piM M Q y :=
      ((HS6.piM_eq_iff hyM hnM').mpr hyq).symm
    rw [hpi]
    exact HS6.piM_mem_bar hy hyM
  · intro hx
    obtain ⟨n, hnCN, hnM, hxeq⟩ := (HS6.mem_bar (S := hc.CN t) (x : Mbar M Q)).mp x.2
    have hxsub : (⟨HS6.piM M Q n, HS6.piM_mem_bar hnCN hnM⟩ :
        ↥(bar M Q (hc.CN t))) = x := Subtype.ext hxeq
    rw [← hxsub] at hx ⊢
    apply Multiplicative.toAdd.injective
    rw [D.mu_piM AM hnCN]
    show D.muVec AM ⟨n, hnCN⟩ = Multiplicative.toAdd (1 : Multiplicative (Fin 3 → AM.K))
    rw [show Multiplicative.toAdd (1 : Multiplicative (Fin 3 → AM.K)) = 0 from rfl]
    apply (D.muVec_eq_zero_iff_phiMat AM ⟨n, hnCN⟩).mpr
    obtain ⟨y, hy, hyM, hpy⟩ := (HS6.mem_bar _).mp hx
    have hnM' : n ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hnCN).1
    have hq : y⁻¹ * n ∈ Q := (HS6.piM_eq_iff hyM hnM').mp hpy
    exact (D.phiMat_eq_zero_iff_root AM hnCN).mpr ⟨y, hy, hq⟩

private theorem Sec108Data.rhoMat_body (r : ↥(Rt M (LB M Q B) t)) :
    D.rhoMat AM r =
      (((D.frameB AM)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) AM.K) :
        Matrix (Fin 3) (Fin 3) AM.K) * D.matV AM ⟨(r : G), D.Rt_le_H0 r.2⟩ *
        (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) := rfl

private theorem Sec108Data.rho_mat_eq [(Q.subgroupOf M).Normal] {r : G}
    (hr : r ∈ Rt M (LB M Q B) t)
    (h : HS6.piM M Q r ∈ bar M Q (Rt M (LB M Q B) t)) :
    ((D.rho AM ⟨HS6.piM M Q r, h⟩ : GL (Fin 3) AM.K) :
        Matrix (Fin 3) (Fin 3) AM.K) =
      (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)⁻¹ *
        D.matV AM ⟨r, D.Rt_le_H0 hr⟩ *
        (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) := by
  rw [D.rho_piM AM hr h, Sec108Data.rhoMat_body D AM ⟨r, hr⟩,
    Matrix.SpecialLinearGroup.coe_inv]
  have hP : (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K).adjugate =
      (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)⁻¹ := by
    have hPdet : (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K).det = 1 := (D.frameB AM).2
    have hmul : (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K).adjugate *
        (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) = 1 := by
      simpa [hPdet] using Matrix.adjugate_mul (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)
    exact (Matrix.inv_eq_left_inv hmul).symm
  rw [hP]

private theorem Sec108Data.rho_inv_transpose_eq [(Q.subgroupOf M).Normal] {r : G}
    (hr : r ∈ Rt M (LB M Q B) t)
    (h : HS6.piM M Q r ∈ bar M Q (Rt M (LB M Q B) t)) :
    (((D.rho AM ⟨HS6.piM M Q r, h⟩)⁻¹ : GL (Fin 3) AM.K) :
        Matrix (Fin 3) (Fin 3) AM.K)ᵀ =
      (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)ᵀ *
        (D.matV AM ⟨r, D.Rt_le_H0 hr⟩)⁻¹ᵀ *
        ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)ᵀ)⁻¹ := by
  have hPt : IsUnit ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)ᵀ).det := by
    rw [Matrix.det_transpose]
    change IsUnit ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K).det)
    rw [(D.frameB AM).2]
    exact isUnit_one
  rw [Matrix.GeneralLinearGroup.coe_inv, Sec108Data.rho_mat_eq D AM hr h,
    Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  rw [Matrix.nonsing_inv_nonsing_inv _ hPt]

private theorem mulVec_conj_cancel {K : Type} [Field K] (P M : Matrix (Fin 3) (Fin 3) K)
    (hP : P.det = 1) (a : Fin 3 → K) :
    (Pᵀ * M * (Pᵀ)⁻¹) *ᵥ (Pᵀ *ᵥ a) = Pᵀ *ᵥ (M *ᵥ a) := by
  have hPt : IsUnit (Pᵀ).det := by
    rw [Matrix.det_transpose, hP]
    exact isUnit_one
  calc
    (Pᵀ * M * (Pᵀ)⁻¹) *ᵥ (Pᵀ *ᵥ a)
        = ((Pᵀ * M * (Pᵀ)⁻¹) * Pᵀ) *ᵥ a := by rw [Matrix.mulVec_mulVec]
    _ = (Pᵀ * M) *ᵥ a := by
          rw [Matrix.nonsing_inv_mul_cancel_right (Pᵀ) (Pᵀ * M) hPt]
    _ = Pᵀ *ᵥ (M *ᵥ a) := by rw [Matrix.mulVec_mulVec]

private theorem Sec108Data.muVec_conj [(Q.subgroupOf M).Normal] {r n : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hn : n ∈ hc.CN t)
    (h : HS6.piM M Q r ∈ bar M Q (Rt M (LB M Q B) t)) :
    D.muVec AM ⟨r * n * r⁻¹, D.conj_mem_CN hr hn⟩ =
      (((D.rho AM ⟨HS6.piM M Q r, h⟩)⁻¹ : GL (Fin 3) AM.K) :
        Matrix (Fin 3) (Fin 3) AM.K)ᵀ *ᵥ D.muVec AM ⟨n, hn⟩ := by
  let P : Matrix (Fin 3) (Fin 3) AM.K := (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)
  let A : Matrix (Fin 3) (Fin 3) AM.K := D.matV AM ⟨r, D.Rt_le_H0 hr⟩
  let a : Fin 3 → AM.K := ![D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 2 1,
    D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 0 2, D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ 1 0]
  change Pᵀ *ᵥ ![D.phiMat AM ⟨r * n * r⁻¹, D.CN_le_H0 (D.conj_mem_CN hr hn)⟩ 2 1,
      D.phiMat AM ⟨r * n * r⁻¹, D.CN_le_H0 (D.conj_mem_CN hr hn)⟩ 0 2,
      D.phiMat AM ⟨r * n * r⁻¹, D.CN_le_H0 (D.conj_mem_CN hr hn)⟩ 1 0] =
    (((D.rho AM ⟨HS6.piM M Q r, h⟩)⁻¹ : GL (Fin 3) AM.K) :
      Matrix (Fin 3) (Fin 3) AM.K)ᵀ *ᵥ (Pᵀ *ᵥ a)
  have hsym : (D.phiMat AM ⟨n, D.CN_le_H0 hn⟩)ᵀ =
      D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ :=
    D.phiMat_transpose AM (fun e he => D.fix_Vsp_of_mem_CN AM hn he)
      (D.comm_t_of_mem_CN AM hn)
  have hcross : D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ =
      CFSG.LinearAlgebra.crossMatrix a := by
    refine CFSG.LinearAlgebra.eq_crossMatrix ?_ (fun i => D.phiMat_diag AM hn i)
    simpa [CharTwo.neg_eq] using hsym
  have hconj := D.phiMat_conj AM (m := ⟨n, D.CN_le_H0 hn⟩) (r := ⟨r, D.Rt_le_H0 hr⟩)
    (fun e => Sec108Data.phi_comm_of_comm_mem AM (m := ⟨r, D.Rt_le_H0 hr⟩)
      (m' := ⟨t, D.t_mem_H0⟩) (hc.Rt_comm_mem_Q hr) e)
    (fun j => D.phi_bV_eq_sum AM (m := ⟨r, D.Rt_le_H0 hr⟩)
      (fun e he => D.phi_mem_Vsp AM (m := ⟨r, D.Rt_le_H0 hr⟩) hr he) j)
    (fun e he => D.fix_Vsp_of_mem_CN AM hn he) (D.comm_t_of_mem_CN AM hn)
  have harg : (⟨r, D.Rt_le_H0 hr⟩ * ⟨n, D.CN_le_H0 hn⟩ *
      ⟨r, D.Rt_le_H0 hr⟩⁻¹ : ↥(H0 M Z)) =
      ⟨r * n * r⁻¹, D.CN_le_H0 (D.conj_mem_CN hr hn)⟩ := Subtype.ext rfl
  rw [harg] at hconj
  have hcross' : D.phiMat AM ⟨r * n * r⁻¹, D.CN_le_H0 (D.conj_mem_CN hr hn)⟩ =
      CFSG.LinearAlgebra.crossMatrix (A.adjugateᵀ *ᵥ a) := by
    rw [hconj, hcross, CFSG.LinearAlgebra.mul_crossMatrix_mul_transpose]
  rw [hcross', crossMatrix_axis]
  have hAdet : A.det = 1 := D.det_matV_eq_one AM hr
  have hAmul : A * A.adjugate = 1 := by
    simpa [hAdet] using Matrix.mul_adjugate A
  have hAinv : A⁻¹ = A.adjugate := Matrix.inv_eq_right_inv hAmul
  have hAadj : A.adjugateᵀ = A⁻¹ᵀ := by rw [hAinv]
  have hPdet : P.det = 1 := (D.frameB AM).2
  rw [Sec108Data.rho_inv_transpose_eq D AM hr h, hAadj]
  exact (mulVec_conj_cancel P (A⁻¹)ᵀ hPdet a).symm

theorem Sec108Data.mu_conj (r : Mbar M Q) (hr : r ∈ bar M Q (Rt M (LB M Q B) t)) (n : Mbar M Q)
    (hn : n ∈ bar M Q (hc.CN t)) (n' : Mbar M Q) (hn' : n' ∈ bar M Q (hc.CN t))
    (h : n' = r * n * r⁻¹) :
    Multiplicative.toAdd (D.mu AM ⟨n', hn'⟩) =
      (((D.rho AM ⟨r, hr⟩)⁻¹ : GL (Fin 3) AM.K) : Matrix (Fin 3) (Fin 3) AM.K)ᵀ *ᵥ
        Multiplicative.toAdd (D.mu AM ⟨n, hn⟩) := by
  obtain ⟨r₀, hrR, hrM, rfl⟩ := (HS6.mem_bar (S := Rt M (LB M Q B) t) r).mp hr
  obtain ⟨n₀, hnCN, hnM, rfl⟩ := (HS6.mem_bar (S := hc.CN t) n).mp hn
  let n₁ : G := r₀ * n₀ * r₀⁻¹
  have hn₁CN : n₁ ∈ hc.CN t := D.conj_mem_CN hrR hnCN
  have hn₁M : n₁ ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hn₁CN).1
  have hpi : HS6.piM M Q n₁ = n' := by
    rw [h]
    exact HS6.piM_conj hrM hnM
  have hsub : (⟨n', hn'⟩ : ↥(bar M Q (hc.CN t))) =
      ⟨HS6.piM M Q n₁, HS6.piM_mem_bar hn₁CN hn₁M⟩ := Subtype.ext hpi.symm
  have hmemN : HS6.piM M Q n₀ ∈ bar M Q (hc.CN t) := HS6.piM_mem_bar hnCN hnM
  rw [hsub, D.mu_piM AM hn₁CN, D.mu_piM AM hnCN hmemN]
  exact D.muVec_conj AM hrR hnCN (HS6.piM_mem_bar hrR (hc.Rt_le_M t hrR))

private theorem Sec108Data.muVec_zero_eq_dotProduct (n : ↥(hc.CN t)) :
    D.muVec AM n 0 =
      ![D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ 2 1,
        D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ 0 2,
        D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ 1 0] ⬝ᵥ
        ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ Sec108.e₀ AM.K) := by
  simp [Sec108Data.muVec, Matrix.mulVec, dotProduct, Sec108.e₀, Fin.sum_univ_three, mul_comm]

theorem Sec108Data.mem_bar_LB_iff_mu (n : Mbar M Q) (hn : n ∈ bar M Q (hc.CN t)) :
    n ∈ bar M Q (LB M Q B) ↔ Multiplicative.toAdd (D.mu AM ⟨n, hn⟩) 0 = 0 := by
  obtain ⟨n₀, hnCN, hnM, hxeq⟩ := (HS6.mem_bar (S := hc.CN t) n).mp hn
  have hmem : HS6.piM M Q n₀ ∈ bar M Q (hc.CN t) := HS6.piM_mem_bar hnCN hnM
  have hmu : Multiplicative.toAdd (D.mu AM ⟨n, hn⟩) = D.muVec AM ⟨n₀, hnCN⟩ := by
    have hsub : (⟨HS6.piM M Q n₀, hmem⟩ : ↥(bar M Q (hc.CN t))) = ⟨n, hn⟩ :=
      Subtype.ext hxeq
    rw [← hsub]
    exact D.mu_piM AM hnCN hmem
  set P : Matrix (Fin 3) (Fin 3) AM.K := (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) with hP
  set β : Fin 3 → AM.K := P *ᵥ Sec108.e₀ AM.K with hβdef
  have hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM := by
    simpa [β, P] using D.frameB_mem_Bsp AM
  have hβ : β ≠ 0 := by
    intro h0
    have he0 : Sec108.e₀ AM.K ≠ 0 := by
      intro h
      have := congrFun h 0
      simpa [Sec108.e₀] using this
    have hPdet : P.det = 1 := (D.frameB AM).2
    have h3 : P⁻¹ *ᵥ β = Sec108.e₀ AM.K := by
      rw [hβdef, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (by rw [hPdet]; exact isUnit_one), Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h3
    exact he0 h3.symm
  have hLHS : n ∈ bar M Q (LB M Q B) ↔
      HS6.piM M Q n₀ ∈ bar M Q (LB M Q B) := by rw [hxeq]
  rw [hLHS, HS6.piM_mem_bar_iff sec39_Q_le_LB hnM, hmu,
    D.muVec_zero_eq_dotProduct AM ⟨n₀, hnCN⟩]
  exact (D.mem_LB_iff_dotProduct AM hβ hβB hnCN)

end Mu

end CFSG.RankThree.GF2n.Stroth80
