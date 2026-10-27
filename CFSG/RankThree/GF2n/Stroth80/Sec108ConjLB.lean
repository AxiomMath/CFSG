module

public import CFSG.RankThree.GF2n.Stroth80.Sec108PhiL8

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

private theorem matV_inv (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {m : G} (hm : m ∈ Rt M (LB M Q B) t) :
    D.matV AM ⟨m⁻¹, D.Rt_le_H0 ((Rt M (LB M Q B) t).inv_mem hm)⟩ =
      (D.matV AM ⟨m, D.Rt_le_H0 hm⟩)⁻¹ := by
  have h₁ := D.matV_mul AM (m := ⟨m, D.Rt_le_H0 hm⟩)
    (m' := ⟨m⁻¹, D.Rt_le_H0 ((Rt M (LB M Q B) t).inv_mem hm)⟩)
    (fun e he => D.phi_mem_Vsp AM ((Rt M (LB M Q B) t).inv_mem hm) he)
  have h₂ : D.matV AM (⟨m, D.Rt_le_H0 hm⟩ *
      ⟨m⁻¹, D.Rt_le_H0 ((Rt M (LB M Q B) t).inv_mem hm)⟩) = 1 := by
    convert D.matV_one AM using 2
    ext
    simp
  rw [h₂] at h₁
  exact (Matrix.inv_eq_right_inv h₁.symm).symm

private theorem matV_conj (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {r x : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hx : x ∈ Rt M (LB M Q B) t) :
    D.matV AM ⟨r * x * r⁻¹, D.Rt_le_H0 ((Rt M (LB M Q B) t).mul_mem
      ((Rt M (LB M Q B) t).mul_mem hr hx) ((Rt M (LB M Q B) t).inv_mem hr))⟩ =
      D.matV AM ⟨r, D.Rt_le_H0 hr⟩ * D.matV AM ⟨x, D.Rt_le_H0 hx⟩ *
        (D.matV AM ⟨r, D.Rt_le_H0 hr⟩)⁻¹ := by
  have h₁ := D.matV_mul AM (m := ⟨r * x, D.Rt_le_H0 ((Rt M (LB M Q B) t).mul_mem hr hx)⟩)
    (m' := ⟨r⁻¹, D.Rt_le_H0 ((Rt M (LB M Q B) t).inv_mem hr)⟩)
    (fun e he => D.phi_mem_Vsp AM ((Rt M (LB M Q B) t).inv_mem hr) he)
  have h₂ := D.matV_mul AM (m := ⟨r, D.Rt_le_H0 hr⟩) (m' := ⟨x, D.Rt_le_H0 hx⟩)
    (fun e he => D.phi_mem_Vsp AM hx he)
  have hconv : D.matV AM ⟨r * x * r⁻¹, D.Rt_le_H0 ((Rt M (LB M Q B) t).mul_mem
      ((Rt M (LB M Q B) t).mul_mem hr hx) ((Rt M (LB M Q B) t).inv_mem hr))⟩ =
      D.matV AM (⟨r * x, D.Rt_le_H0 ((Rt M (LB M Q B) t).mul_mem hr hx)⟩ *
        ⟨r⁻¹, D.Rt_le_H0 ((Rt M (LB M Q B) t).inv_mem hr)⟩) := by
    congr 1
  have hconv2 : D.matV AM ⟨r * x, D.Rt_le_H0 ((Rt M (LB M Q B) t).mul_mem hr hx)⟩ =
      D.matV AM (⟨r, D.Rt_le_H0 hr⟩ * ⟨x, D.Rt_le_H0 hx⟩) := by
    congr 1
  rw [hconv, h₁, hconv2, h₂, matV_inv D AM hr]

private theorem matV_sq_eq_one (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {i : G}
    (hi : i ∈ Rt M (LB M Q B) t) (h2 : i ^ 2 ∈ Q) :
    D.matV AM ⟨i, D.Rt_le_H0 hi⟩ * D.matV AM ⟨i, D.Rt_le_H0 hi⟩ = 1 := by
  have hii : i * i ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).mul_mem hi hi
  have hsq : D.matV AM ⟨i * i, D.Rt_le_H0 hii⟩ = 1 := by
    rw [D.matV_eq_one_iff AM (m := ⟨i * i, D.Rt_le_H0 hii⟩)
      (fun e he => D.phi_mem_Vsp AM hii he)]
    intro e he
    have hphi : AM.φ ⟨i * i, D.Rt_le_H0 hii⟩ = 1 :=
      (AM.φ_ker _).mpr (by simpa [pow_two] using h2)
    rw [hphi]
    rfl
  rw [← D.matV_mul AM (m := ⟨i, D.Rt_le_H0 hi⟩) (m' := ⟨i, D.Rt_le_H0 hi⟩)
    (fun e he => D.phi_mem_Vsp AM hi he)]
  simpa using hsq

private theorem adjugate_adjugate_transpose {K : Type} [Field K]
    {C : Matrix (Fin 3) (Fin 3) K} (hC : C.det = 1) :
    (Matrix.adjugate (Matrix.adjugate Cᵀ))ᵀ = C := by
  have hCt : Cᵀ.det = 1 := by rw [Matrix.det_transpose, hC]
  have hD : Matrix.adjugate Cᵀ * Cᵀ = 1 := by
    rw [Matrix.adjugate_mul, hCt]
    simp
  have hdetD : (Matrix.adjugate Cᵀ).det = 1 := by
    rw [Matrix.det_adjugate, hCt]
    norm_num
  have hE : Matrix.adjugate Cᵀ * Matrix.adjugate (Matrix.adjugate Cᵀ) = 1 := by
    rw [Matrix.mul_adjugate, hdetD]
    simp
  have h1 : Matrix.adjugate (Matrix.adjugate Cᵀ) = Cᵀ :=
    (Matrix.inv_eq_right_inv hE).symm.trans (Matrix.inv_eq_right_inv hD)
  rw [h1, Matrix.transpose_transpose]

private theorem exists_conj_matV_eq_one_add (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {i : G}
    (hi : i ∈ Rt M (LB M Q B) t) (h2 : i ^ 2 ∈ Q) {β : Fin 3 → AM.K} (hβ : β ≠ 0)
    (hβB : ∑ j, β j • (D.bV AM j : AM.M₀.E) ∈ D.Bsp AM) :
    ∃ r, ∃ hr : r ∈ Rt M (LB M Q B) t, ∃ μ : Fin 3 → AM.K, μ ⬝ᵥ β = 0 ∧
      D.matV AM ⟨r * i * r⁻¹, D.Rt_le_H0 ((Rt M (LB M Q B) t).mul_mem
        ((Rt M (LB M Q B) t).mul_mem hr hi) ((Rt M (LB M Q B) t).inv_mem hr))⟩ =
        1 + Matrix.vecMulVec β μ := by
  let I := D.matV AM ⟨i, D.Rt_le_H0 hi⟩
  have hII : I * I = 1 := matV_sq_eq_one D AM hi h2
  have hdet : I.det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hII
    rw [Matrix.det_mul, Matrix.det_one, h0, zero_mul] at h
    exact zero_ne_one h
  let iGL : GL (Fin 3) AM.K := Matrix.GeneralLinearGroup.mkOfDetNeZero I hdet
  have hiGL : iGL * iGL = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro a b
    have h := congrFun (congrFun hII a) b
    simpa [iGL] using h
  obtain ⟨g, hgSL, μ, hμβ, hgI⟩ :=
    CFSG.ClassicalGroups.SpecialLinear.exists_conj_eq_one_add_vecMulVec
      (K := AM.K) (m := 3) (by norm_num) (by norm_num) hβ hiGL
  have hgdet : (g : Matrix (Fin 3) (Fin 3) AM.K).det = 1 :=
    CFSG.Open.StatedAPI.det_of_mem_statedSL hgSL
  let gSL : Matrix.SpecialLinearGroup (Fin 3) AM.K := ⟨(g : Matrix (Fin 3) (Fin 3) AM.K), hgdet⟩
  obtain ⟨r, ⟨hrR, hrt⟩, hrH, hr⟩ := D.bV_spec AM gSL
  have hmatVr : D.matV AM ⟨r, D.Rt_le_H0 hrR⟩ = (g : Matrix (Fin 3) (Fin 3) AM.K) :=
    D.matV_eq_of_forall AM hr
  have hmatVi' : D.matV AM ⟨r * i * r⁻¹, D.Rt_le_H0 ((Rt M (LB M Q B) t).mul_mem
      ((Rt M (LB M Q B) t).mul_mem hrR hi) ((Rt M (LB M Q B) t).inv_mem hrR))⟩ =
      (g : Matrix (Fin 3) (Fin 3) AM.K) * I * (g : Matrix (Fin 3) (Fin 3) AM.K)⁻¹ := by
    have h := matV_conj D AM (r := r) (x := i) hrR hi
    rwa [hmatVr] at h
  have hmatVi'_eq : D.matV AM ⟨r * i * r⁻¹, D.Rt_le_H0 ((Rt M (LB M Q B) t).mul_mem
      ((Rt M (LB M Q B) t).mul_mem hrR hi) ((Rt M (LB M Q B) t).inv_mem hrR))⟩ =
      1 + Matrix.vecMulVec β μ := by
    rw [hmatVi']
    simpa [iGL, Matrix.GeneralLinearGroup.coe_inv] using hgI
  exact ⟨r, hrR, μ, hμβ, hmatVi'_eq⟩

private theorem mem_LB_of_phiMat_eq_crossMatrix (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {β : Fin 3 → AM.K} (hβ : β ≠ 0)
    (hβB : ∑ j, β j • (D.bV AM j : AM.M₀.E) ∈ D.Bsp AM) {n : G} (hn : n ∈ hc.CN t)
    {a : Fin 3 → AM.K} (hS : D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ =
      CFSG.LinearAlgebra.crossMatrix a) (ha : a ⬝ᵥ β = 0) :
    n ∈ LB M Q B := by
  refine (D.mem_LB_iff_dotProduct AM hβ hβB hn).mpr ?_
  rw [hS]
  have haxis : ![CFSG.LinearAlgebra.crossMatrix a 2 1,
      CFSG.LinearAlgebra.crossMatrix a 0 2,
      CFSG.LinearAlgebra.crossMatrix a 1 0] = a := by
    ext i
    fin_cases i <;> simp [CFSG.LinearAlgebra.crossMatrix, CharTwo.neg_eq]
  rw [haxis]
  exact ha

private theorem exists_conj_mem_LB_of_mem_CN_of_ne_zero (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {n : G} (hn : n ∈ hc.CN t)
    {β : Fin 3 → AM.K} (hβ : β ≠ 0)
    (hβB : ∑ j, β j • (D.bV AM j : AM.M₀.E) ∈ D.Bsp AM) {a : Fin 3 → AM.K}
    (ha : a ≠ 0) (hS : D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ =
      CFSG.LinearAlgebra.crossMatrix a) :
    ∃ r, ∃ hr : r ∈ Rt M (LB M Q B) t, r * n * r⁻¹ ∈ LB M Q B := by
  obtain ⟨a', ha'ne, ha'β⟩ := CFSG.LinearAlgebra.exists_ne_zero_dotProduct_eq_zero β
  obtain ⟨C, hCSL, hCa⟩ := exists_statedSL_mulVec_eq (m := 3) (by norm_num) ha'ne ha
  have hCdet : (C : Matrix (Fin 3) (Fin 3) AM.K).det = 1 :=
    CFSG.Open.StatedAPI.det_of_mem_statedSL hCSL
  let Dm : Matrix (Fin 3) (Fin 3) AM.K := Matrix.adjugate (C : Matrix (Fin 3) (Fin 3) AM.K)ᵀ
  have hdetD : Dm.det = 1 := by
    dsimp [Dm]
    rw [Matrix.det_adjugate, Matrix.det_transpose, hCdet]
    norm_num
  have hAadj : (Matrix.adjugate Dm)ᵀ = (C : Matrix (Fin 3) (Fin 3) AM.K) := by
    simpa [Dm] using adjugate_adjugate_transpose hCdet
  let A : Matrix.SpecialLinearGroup (Fin 3) AM.K := ⟨Dm, hdetD⟩
  obtain ⟨r', ⟨hr'R, hr't⟩, hr'H, hr'⟩ := D.bV_spec AM A
  have hr'comm : ∀ e, AM.φ ⟨r', hr'H⟩ (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨r', hr'H⟩ e) :=
    fun e => Sec108Data.phi_comm_of_comm_mem AM (D.comm_Rt_root_mem r' hr'R t D.sit.mem) e
  have hconj := D.phiMat_conj AM (m := ⟨n, D.CN_le_H0 hn⟩) (r := ⟨r', hr'H⟩)
    (hr := hr'comm) (A := Dm) (hA := hr')
    (hV := fun e he => D.fix_Vsp_of_mem_CN AM hn he)
    (ht := fun e => D.comm_t_of_mem_CN AM hn e)
  have hi''CN : r' * n * r'⁻¹ ∈ hc.CN t := D.conj_mem_CN hr'R hn
  have hS' : D.phiMat AM ⟨r' * n * r'⁻¹, D.CN_le_H0 hi''CN⟩ =
      CFSG.LinearAlgebra.crossMatrix a' := by
    have h := hconj
    rw [hS, CFSG.LinearAlgebra.mul_crossMatrix_mul_transpose, hAadj, hCa] at h
    have harg : D.phiMat AM (⟨r', hr'H⟩ * ⟨n, D.CN_le_H0 hn⟩ * ⟨r', hr'H⟩⁻¹) =
        D.phiMat AM ⟨r' * n * r'⁻¹, D.CN_le_H0 hi''CN⟩ := by
      congr 1
    rwa [harg] at h
  exact ⟨r', hr'R, mem_LB_of_phiMat_eq_crossMatrix D AM hβ hβB hi''CN hS' ha'β⟩

private theorem exists_conj_mem_LB_of_mem_CN (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {n : G} (hn : n ∈ hc.CN t) :
    ∃ r, ∃ hr : r ∈ Rt M (LB M Q B) t, r * n * r⁻¹ ∈ LB M Q B := by
  obtain ⟨β, hβ, hβB⟩ := D.exists_coord_Bsp AM
  let S : Matrix (Fin 3) (Fin 3) AM.K := D.phiMat AM ⟨n, D.CN_le_H0 hn⟩
  have hSsym : Sᵀ = S := D.phiMat_transpose AM (m := ⟨n, D.CN_le_H0 hn⟩)
    (fun e he => D.fix_Vsp_of_mem_CN AM hn he) (fun e => D.comm_t_of_mem_CN AM hn e)
  have hSskew : Sᵀ = -S := by
    rw [hSsym]
    exact (CharTwo.neg_eq S).symm
  have hSdiag : ∀ i, S i i = 0 := fun i => D.phiMat_diag AM (n := n) hn i
  let a : Fin 3 → AM.K := ![S 2 1, S 0 2, S 1 0]
  have hScross : S = CFSG.LinearAlgebra.crossMatrix a :=
    CFSG.LinearAlgebra.eq_crossMatrix hSskew hSdiag
  by_cases ha : a = 0
  · have hS0 : S = 0 := by
      rw [hScross, ha]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [CFSG.LinearAlgebra.crossMatrix]
    have hS0' : D.phiMat AM ⟨n, D.CN_le_H0 hn⟩ = 0 := hS0
    obtain ⟨y, hyY, hyQ⟩ := (D.phiMat_eq_zero_iff_root AM hn).mp hS0'
    have hmemLB : n ∈ LB M Q B := by
      have heq : n = y * (y⁻¹ * n) := by group
      rw [heq]
      exact (LB M Q B).mul_mem (D.root_le_LB hyY) (Subgroup.mem_sup_left hyQ)
    exact ⟨1, (Rt M (LB M Q B) t).one_mem, by simpa using hmemLB⟩
  · obtain ⟨r, hrR, hmem⟩ :=
      exists_conj_mem_LB_of_mem_CN_of_ne_zero D AM hn hβ hβB ha hScross
    exact ⟨r, hrR, hmem⟩

private theorem exists_conj_mem_sup (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {i : G}
    (hi : i ∈ Rt M (LB M Q B) t) (h2 : i ^ 2 ∈ Q) :
    ∃ r, ∃ hr : r ∈ Rt M (LB M Q B) t,
      r * i * r⁻¹ ∈ hc.CN t ⊔ LB M Q B := by
  obtain ⟨β, hβ, hβB⟩ := D.exists_coord_Bsp AM
  obtain ⟨r, hrR, μ, hμβ, hmatVi'⟩ := exists_conj_matV_eq_one_add D AM hi h2 hβ hβB
  obtain ⟨l, hl, hmatVl⟩ := D.exists_LB_matV AM hβ hβB hμβ
  let i' := r * i * r⁻¹
  have hi'R : i' ∈ Rt M (LB M Q B) t :=
    (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem hrR hi)
      ((Rt M (LB M Q B) t).inv_mem hrR)
  have hlR : l ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) D.good.1.mem_LB hl
  have hdR : l⁻¹ * i' ∈ Rt M (LB M Q B) t :=
    (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).inv_mem hlR) hi'R
  have hmatVlR : D.matV AM ⟨l, D.Rt_le_H0 hlR⟩ = 1 + Matrix.vecMulVec β μ := by
    simpa using hmatVl
  have hlinv : D.matV AM ⟨l⁻¹, D.Rt_le_H0 ((Rt M (LB M Q B) t).inv_mem hlR)⟩ =
      (D.matV AM ⟨l, D.Rt_le_H0 hlR⟩)⁻¹ := matV_inv D AM hlR
  have hprod : (D.matV AM ⟨l, D.Rt_le_H0 hlR⟩)⁻¹ * D.matV AM ⟨l, D.Rt_le_H0 hlR⟩ = 1 := by
    have hmul := D.matV_mul AM
      (m := ⟨l⁻¹, D.Rt_le_H0 ((Rt M (LB M Q B) t).inv_mem hlR)⟩)
      (m' := ⟨l, D.Rt_le_H0 hlR⟩) (fun e he => D.phi_mem_Vsp AM hlR he)
    have hll : D.matV AM (⟨l⁻¹, D.Rt_le_H0 ((Rt M (LB M Q B) t).inv_mem hlR)⟩ *
        ⟨l, D.Rt_le_H0 hlR⟩) = 1 := by
      convert D.matV_one AM using 2
      ext
      simp
    rw [← hlinv, ← hmul]
    exact hll
  have hmatVd : D.matV AM ⟨l⁻¹ * i', D.Rt_le_H0 hdR⟩ = 1 := by
    have hmul := D.matV_mul AM
      (m := ⟨l⁻¹, D.Rt_le_H0 ((Rt M (LB M Q B) t).inv_mem hlR)⟩)
      (m' := ⟨i', D.Rt_le_H0 hi'R⟩) (fun e he => D.phi_mem_Vsp AM hi'R he)
    rw [show ⟨l⁻¹ * i', D.Rt_le_H0 hdR⟩ =
        ⟨l⁻¹, D.Rt_le_H0 ((Rt M (LB M Q B) t).inv_mem hlR)⟩ *
          ⟨i', D.Rt_le_H0 hi'R⟩ from Subtype.ext rfl,
      hmul, hlinv, hmatVi', ← hmatVlR, hprod]
  have hfix : ∀ e ∈ AM.Vsp hc t, AM.φ ⟨l⁻¹ * i', D.Rt_le_H0 hdR⟩ e = e :=
    (D.matV_eq_one_iff AM (m := ⟨l⁻¹ * i', D.Rt_le_H0 hdR⟩)
      (fun e he => D.phi_mem_Vsp AM hdR he)).mp hmatVd
  have hdCN : l⁻¹ * i' ∈ hc.CN t :=
    Ctx.mem_CN.mpr ⟨hdR, hc.comm_Vt_of_fix AM (D.Rt_le_H0 hdR) hfix⟩
  refine ⟨r, hrR, ?_⟩
  have heq : r * i * r⁻¹ = l * (l⁻¹ * i') := by
    change r * i * r⁻¹ = l * (l⁻¹ * (r * i * r⁻¹))
    group
  rw [heq, sup_comm]
  exact Subgroup.mul_mem_sup hl hdCN

theorem Sec108Data.exists_conj_mem_LB (D : Sec108Data hc t Y) {i : G}
    (hi : i ∈ Rt M (LB M Q B) t) (h2 : i ^ 2 ∈ Q) :
    ∃ r ∈ Rt M (LB M Q B) t, r * i * r⁻¹ ∈ LB M Q B := by
  obtain ⟨AM⟩ := Smith81.Smith23E1.ActionModel.nonempty hc.hyp
  let R := Rt M (LB M Q B) t
  obtain ⟨r, hrR, hi'⟩ := exists_conj_mem_sup D AM hi h2
  have hi'R : r * i * r⁻¹ ∈ R := R.mul_mem (R.mul_mem hrR hi) (R.inv_mem hrR)
  have h2' : (r * i * r⁻¹) ^ 2 ∈ Q := by
    have heq : (r * i * r⁻¹) ^ 2 = r * i ^ 2 * r⁻¹ := by
      rw [pow_two, pow_two]
      group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hrR))
      (i ^ 2)).mp h2
  rcases D.mem_or_mem_of_sq_mem hi' h2' with hi'CN | hi'LB
  · obtain ⟨r', hr'R, hmem⟩ := exists_conj_mem_LB_of_mem_CN D AM hi'CN
    refine ⟨r' * r, R.mul_mem hr'R hrR, ?_⟩
    have heq : (r' * r) * i * (r' * r)⁻¹ = r' * (r * i * r⁻¹) * r'⁻¹ := by group
    rw [heq]
    exact hmem
  · exact ⟨r, hrR, hi'LB⟩

end CFSG.RankThree.GF2n.Stroth80
