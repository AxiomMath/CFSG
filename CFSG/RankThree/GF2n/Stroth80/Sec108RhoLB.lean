module

public import CFSG.RankThree.GF2n.Stroth80.Sec108Rho

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G} [(Q.subgroupOf M).Normal]
  (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)

private theorem frameB_mulVec_e0_ne_zero :
    (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ Sec108.e₀ AM.K ≠ 0 := by
  intro h
  have hPP : (((D.frameB AM)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) AM.K) :
        Matrix (Fin 3) (Fin 3) AM.K) *
      (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_mul]
    simp
  have he0 : Sec108.e₀ AM.K = 0 := by
    calc Sec108.e₀ AM.K = (1 : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ Sec108.e₀ AM.K := by
          rw [Matrix.one_mulVec]
      _ = ((((D.frameB AM)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) AM.K) :
        Matrix (Fin 3) (Fin 3) AM.K) *
          (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)) *ᵥ Sec108.e₀ AM.K := by rw [hPP]
      _ = (((D.frameB AM)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) AM.K) :
        Matrix (Fin 3) (Fin 3) AM.K) *ᵥ
          ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ Sec108.e₀ AM.K) := by
          rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [h, Matrix.mulVec_zero]
  have h0 := congrFun he0 0
  simp [Sec108.e₀] at h0

private theorem frame_conj_vecMulVec {K : Type} [Field K]
    (P : Matrix.SpecialLinearGroup (Fin 3) K) (u : Fin 3 → K) :
    ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (1 + Matrix.vecMulVec ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ Sec108.e₀ K) u) *
        (P : Matrix (Fin 3) (Fin 3) K) =
      1 + Matrix.vecMulVec (Sec108.e₀ K) ((P : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ u) := by
  have hPP : ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (P : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_mul]
    simp
  have hPinv : ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ Sec108.e₀ K) = Sec108.e₀ K := by
    rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
  have huv : u ᵥ* (P : Matrix (Fin 3) (Fin 3) K) =
      (P : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ u := by
    simpa using Matrix.vecMul_transpose (A := (P : Matrix (Fin 3) (Fin 3) K)ᵀ) u
  rw [mul_add, add_mul, mul_one, hPP, Matrix.mul_vecMulVec, hPinv,
    Matrix.vecMulVec_mul, huv]

private theorem transpose_mulVec_invTranspose {K : Type} [Field K]
    (P : Matrix.SpecialLinearGroup (Fin 3) K) (u : Fin 3 → K) :
    (P : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ
      ((((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ) *ᵥ u) =
        u := by
  have hPP : ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (P : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_mul]
    simp
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hPP, Matrix.transpose_one,
    Matrix.one_mulVec]

private theorem dotProduct_invTranspose_e0 {K : Type} [Field K]
    (P : Matrix.SpecialLinearGroup (Fin 3) K) (u : Fin 3 → K) :
    ((((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ) *ᵥ u) ⬝ᵥ
      ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ Sec108.e₀ K) = u 0 := by
  have hPP : ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (P : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_mul]
    simp
  calc
    ((((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ) *ᵥ u) ⬝ᵥ
        ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ Sec108.e₀ K) =
      ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ Sec108.e₀ K) ⬝ᵥ
        ((((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ) *ᵥ u) :=
      dotProduct_comm _ _
    _ = u ⬝ᵥ ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ Sec108.e₀ K) := by
      rw [dotProduct_transpose_mulVec]
    _ = u ⬝ᵥ Sec108.e₀ K := by rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
    _ = u 0 := by simp [Sec108.e₀]

private theorem frame_mulVec_e0_of_mulVec_beta {K : Type} [Field K]
    (P : Matrix.SpecialLinearGroup (Fin 3) K) {A : Matrix (Fin 3) (Fin 3) K} {c : K}
    (hA : A *ᵥ ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ Sec108.e₀ K) =
      c • ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ Sec108.e₀ K)) :
    (((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A *
      (P : Matrix (Fin 3) (Fin 3) K)) *ᵥ Sec108.e₀ K = c • Sec108.e₀ K := by
  have hPP : ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (P : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_mul]
    simp
  have hPinv : ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ Sec108.e₀ K) = Sec108.e₀ K := by
    rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, Matrix.mulVec_smul, hPinv]

private theorem mulVec_beta_of_frame_mulVec_e0 {K : Type} [Field K]
    (P : Matrix.SpecialLinearGroup (Fin 3) K) {A : Matrix (Fin 3) (Fin 3) K} {c : K}
    (hRho : (((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A *
      (P : Matrix (Fin 3) (Fin 3) K)) *ᵥ Sec108.e₀ K = c • Sec108.e₀ K) :
    A *ᵥ ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ Sec108.e₀ K) =
      c • ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ Sec108.e₀ K) := by
  have hPP : (P : Matrix (Fin 3) (Fin 3) K) *
      ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.mul_adjugate]
    simp
  have hAP : (P : Matrix (Fin 3) (Fin 3) K) *
      (((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A *
        (P : Matrix (Fin 3) (Fin 3) K)) = A * (P : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Matrix.mul_assoc (P : Matrix (Fin 3) (Fin 3) K)
      (((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A)
      (P : Matrix (Fin 3) (Fin 3) K)]
    rw [← Matrix.mul_assoc (P : Matrix (Fin 3) (Fin 3) K)
      ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) A]
    rw [hPP, Matrix.one_mul]
  calc
    A *ᵥ ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ Sec108.e₀ K) =
        (A * (P : Matrix (Fin 3) (Fin 3) K)) *ᵥ Sec108.e₀ K := by
      rw [Matrix.mulVec_mulVec]
    _ = ((P : Matrix (Fin 3) (Fin 3) K) *
        (((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A *
          (P : Matrix (Fin 3) (Fin 3) K))) *ᵥ Sec108.e₀ K := by rw [hAP]
    _ = (P : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A *
          (P : Matrix (Fin 3) (Fin 3) K)) *ᵥ Sec108.e₀ K) := by
      rw [Matrix.mulVec_mulVec]
    _ = (P : Matrix (Fin 3) (Fin 3) K) *ᵥ (c • Sec108.e₀ K) := by rw [hRho]
    _ = c • ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ Sec108.e₀ K) := by
      rw [Matrix.mulVec_smul]

private theorem mulVec_e0_eq_col {K : Type} [Field K] (A : Matrix (Fin 3) (Fin 3) K) :
    A *ᵥ Sec108.e₀ K = A.col 0 := by
  simpa [Sec108.e₀] using Matrix.mulVec_single_one A 0

theorem Sec108Data.rho_LB (l : Mbar M Q) (hl : l ∈ bar M Q (LB M Q B)) :
    ∃ u : Fin 3 → AM.K, u 0 = 0 ∧
      ((D.rho AM ⟨l, hc.bar_LB_le_bar_Rt D.good.1.mem_LB hl⟩ : GL (Fin 3) AM.K) :
        Matrix (Fin 3) (Fin 3) AM.K) = 1 + Matrix.vecMulVec (Sec108.e₀ AM.K) u := by
  obtain ⟨r, hrLB, hrM, hpi⟩ := (HS6.mem_bar l).mp hl
  subst l
  have hrRt : r ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) D.good.1.mem_LB hrLB
  let β : Fin 3 → AM.K := (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ Sec108.e₀ AM.K
  have hβ : β ≠ 0 := frameB_mulVec_e0_ne_zero D AM
  have hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM := D.frameB_mem_Bsp AM
  obtain ⟨μ, hμβ, hmatV⟩ := D.exists_matV_LB AM hβ hβB hrLB
  have hmatV' : D.matV AM ⟨r, D.Rt_le_H0 hrRt⟩ = 1 + Matrix.vecMulVec β μ := by
    rw [show (⟨r, D.Rt_le_H0 hrRt⟩ : ↥(H0 M Z)) = ⟨r, hc.LB_le_H0 hrLB⟩ from
      Subtype.ext rfl]
    exact hmatV
  refine ⟨(D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)ᵀ *ᵥ μ, ?_, ?_⟩
  · have hdot : ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)ᵀ *ᵥ μ) 0 = μ ⬝ᵥ β := by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm (μ j)]
      congr 1
      simp [β, Sec108.e₀]
    rw [hdot, hμβ]
  · have hrho := D.rho_piM AM hrRt
      (hc.bar_LB_le_bar_Rt D.good.1.mem_LB (by assumption))
    rw [hrho]
    unfold Sec108Data.rhoMat
    rw [hmatV']
    exact frame_conj_vecMulVec (D.frameB AM) μ

theorem Sec108Data.exists_LB_rho (u : Fin 3 → AM.K) (hu : u 0 = 0) :
    ∃ l, ∃ hl : l ∈ bar M Q (LB M Q B),
      ((D.rho AM ⟨l, hc.bar_LB_le_bar_Rt D.good.1.mem_LB hl⟩ : GL (Fin 3) AM.K) :
        Matrix (Fin 3) (Fin 3) AM.K) = 1 + Matrix.vecMulVec (Sec108.e₀ AM.K) u := by
  let P : Matrix.SpecialLinearGroup (Fin 3) AM.K := D.frameB AM
  let β : Fin 3 → AM.K := (P : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ Sec108.e₀ AM.K
  let μ : Fin 3 → AM.K :=
    (((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) AM.K) : Matrix (Fin 3) (Fin 3) AM.K)ᵀ) *ᵥ u
  have hβ : β ≠ 0 := by
    simpa [β, P] using frameB_mulVec_e0_ne_zero D AM
  have hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM := by
    simpa [β, P] using D.frameB_mem_Bsp AM
  have hμ : μ ⬝ᵥ β = 0 := by
    have h := dotProduct_invTranspose_e0 P u
    rw [h, hu]
  obtain ⟨x, hxLB, hmatV⟩ := D.exists_LB_matV AM hβ hβB hμ
  have hxRt : x ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) D.good.1.mem_LB hxLB
  let hl : HS6.piM M Q x ∈ bar M Q (LB M Q B) :=
    HS6.piM_mem_bar (S := LB M Q B) hxLB (hc.LB_le_M hxLB)
  have hmemRt : HS6.piM M Q x ∈ bar M Q (Rt M (LB M Q B) t) :=
    hc.bar_LB_le_bar_Rt D.good.1.mem_LB hl
  refine ⟨HS6.piM M Q x, hl, ?_⟩
  have hrho := D.rho_piM AM hxRt hmemRt
  rw [hrho]
  unfold Sec108Data.rhoMat
  rw [hmatV]
  rw [← transpose_mulVec_invTranspose P u]
  exact frame_conj_vecMulVec P μ

private theorem bV_sum_ne_zero {β : Fin 3 → AM.K} (hβ : β ≠ 0) :
    (∑ i, β i • (D.bV AM i : AM.M₀.E)) ≠ 0 := by
  intro h
  apply hβ
  have hzero : (∑ i, β i • D.bV AM i : ↥(AM.Vsp hc t)) = 0 := by
    apply Subtype.ext
    simpa using h
  have hβ0 := (Fintype.linearIndependent_iffₛ.mp (D.bV AM).linearIndependent) β 0
    (by simpa using hzero)
  refine funext fun i => ?_
  simpa using hβ0 i

private theorem B_eV_sum (β : Fin 3 → AM.K) (i : Fin 3) :
    AM.M₀.B (D.eV AM i) (∑ j, β j • (D.bV AM j : AM.M₀.E)) = β i := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, D.B_eV_bV, mul_ite, mul_one, mul_zero]
  simp

private theorem maps_Bsp_of_mem_normalizer_sup {r : G} (hrH : r ∈ H0 M Z)
    (hrN : r ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G)) :
    ∀ w ∈ D.Bsp AM, AM.φ ⟨r, hrH⟩ w ∈ D.Bsp AM := by
  intro w hw
  obtain ⟨b, hbB, hbQ, hpi⟩ := (D.mem_Bsp AM).mp hw
  have hxN : r * b * r⁻¹ ∈ B ⊔ Z :=
    (Subgroup.mem_normalizer_iff.mp hrN b).mp (Subgroup.mem_sup_left hbB)
  obtain ⟨b', hb'B, z, hzZ, hxeq⟩ := exists_mul_of_mem_sup_of_commute
    (fun b hb z hz => (Smith81.Z_central hc.hyp hz (hc.le hb)).symm) hxN
  rw [D.mem_Bsp AM, ← hpi, ← AM.φ_π ⟨r, hrH⟩ b hbQ, hxeq]
  have hker : AM.M₀.π z = 0 := (AM.M₀.π_ker z (hc.Z_le_Q hzZ)).mpr hzZ
  rw [AM.M₀.π_mul b' (hc.le hb'B) z (hc.Z_le_Q hzZ), hker, add_zero]
  exact AM.M₀.pi_mem_img hb'B (hc.le hb'B)

private theorem mem_normalizer_sup_of_maps_Bsp {r : G} (hrH : r ∈ H0 M Z)
    (hmap : ∀ w ∈ D.Bsp AM, AM.φ ⟨r, hrH⟩ w ∈ D.Bsp AM) :
    r ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨b, hbB, z, hzZ, hxeq⟩ := exists_mul_of_mem_sup_of_commute
    (fun b hb z hz => (Smith81.Z_central hc.hyp hz (hc.le hb)).symm) hx
  rw [hxeq, show r * (b * z) * r⁻¹ = (r * b * r⁻¹) * (r * z * r⁻¹) by group]
  have hwb : AM.M₀.π (r * b * r⁻¹) ∈ D.Bsp AM := by
    have h := hmap (AM.M₀.π b) ((D.mem_Bsp AM).mpr (AM.M₀.pi_mem_img hbB (hc.le hbB)))
    rwa [AM.φ_π ⟨r, hrH⟩ b (hc.le hbB)]
  obtain ⟨b', hb'B, hb'Q, hpi⟩ := (D.mem_Bsp AM).mp hwb
  have hbQ : r * b * r⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hrH.1) b).mp (hc.le hbB)
  have hz : b'⁻¹ * (r * b * r⁻¹) ∈ Z :=
    (AM.M₀.pi_eq_iff hb'Q hbQ).mp hpi
  have hb'Z : r * b * r⁻¹ ∈ B ⊔ Z := by
    rw [show r * b * r⁻¹ = b' * (b'⁻¹ * (r * b * r⁻¹)) by group]
    exact (B ⊔ Z).mul_mem (Subgroup.mem_sup_left hb'B) (Subgroup.mem_sup_right hz)
  have hz' : r * z * r⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hrH.1) z).mp hzZ
  exact (B ⊔ Z).mul_mem hb'Z (Subgroup.mem_sup_right hz')

private theorem matV_mulVec_eq_smul_of_maps_Bsp {r : G} (hrH : r ∈ H0 M Z)
    {β : Fin 3 → AM.K} (hβ : β ≠ 0)
    (hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM)
    (hmap : ∀ w ∈ D.Bsp AM, AM.φ ⟨r, hrH⟩ w ∈ D.Bsp AM) :
    ∃ c : AM.K, D.matV AM ⟨r, hrH⟩ *ᵥ β = c • β := by
  let v : AM.M₀.E := ∑ i, β i • (D.bV AM i : AM.M₀.E)
  have hvne : v ≠ 0 := bV_sum_ne_zero D AM hβ
  have hspan : D.Bsp AM = AM.K ∙ v :=
    eq_span_singleton_of_mem_of_finrank_eq_one (D.finrank_Bsp AM) hβB hvne
  have hvmem : AM.φ ⟨r, hrH⟩ v ∈ AM.K ∙ v := hspan ▸ hmap v hβB
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hvmem
  refine ⟨c, ?_⟩
  have hcoord : ∀ i, (D.matV AM ⟨r, hrH⟩ *ᵥ β) i =
      AM.M₀.B (D.eV AM i) (AM.φ ⟨r, hrH⟩ v) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, D.matV_apply, v, map_sum, map_smul,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  ext i
  rw [hcoord i, ← hc, map_smul, B_eV_sum D AM]
  rfl

private theorem phi_bV_sum_eq_smul {r : G} (hrR : r ∈ Rt M (LB M Q B) t)
    {β : Fin 3 → AM.K} {c : AM.K}
    (hA : D.matV AM ⟨r, D.Rt_le_H0 hrR⟩ *ᵥ β = c • β) :
    AM.φ ⟨r, D.Rt_le_H0 hrR⟩ (∑ i, β i • (D.bV AM i : AM.M₀.E)) =
      c • ∑ i, β i • (D.bV AM i : AM.M₀.E) := by
  let A := D.matV AM ⟨r, D.Rt_le_H0 hrR⟩
  have hsum : ∀ j, AM.φ ⟨r, D.Rt_le_H0 hrR⟩ (D.bV AM j) =
      ∑ i, A i j • (D.bV AM i : AM.M₀.E) :=
    D.phi_bV_eq_sum AM (fun e he => D.phi_mem_Vsp AM hrR he)
  calc
    AM.φ ⟨r, D.Rt_le_H0 hrR⟩ (∑ i, β i • (D.bV AM i : AM.M₀.E)) =
        ∑ j, β j • AM.φ ⟨r, D.Rt_le_H0 hrR⟩ (D.bV AM j) := by
      rw [map_sum]
      simp only [map_smul]
    _ = ∑ j, β j • ∑ i, A i j • (D.bV AM i : AM.M₀.E) := by
      simp only [hsum]
    _ = ∑ i, (∑ j, A i j * β j) • (D.bV AM i : AM.M₀.E) := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      exact Finset.sum_congr rfl fun j _ => mul_comm (β j) (A i j)
    _ = ∑ i, (A *ᵥ β) i • (D.bV AM i : AM.M₀.E) := rfl
    _ = ∑ i, (c * β i) • (D.bV AM i : AM.M₀.E) := by
      rw [hA]
      simp only [Pi.smul_apply, smul_eq_mul]
    _ = c • ∑ i, β i • (D.bV AM i : AM.M₀.E) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]

private theorem maps_Bsp_of_matV_mulVec_eq_smul {r : G} (hrR : r ∈ Rt M (LB M Q B) t)
    {β : Fin 3 → AM.K} (hβ : β ≠ 0)
    (hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM)
    (hA : ∃ c : AM.K, D.matV AM ⟨r, D.Rt_le_H0 hrR⟩ *ᵥ β = c • β) :
    ∀ w ∈ D.Bsp AM, AM.φ ⟨r, D.Rt_le_H0 hrR⟩ w ∈ D.Bsp AM := by
  obtain ⟨c, hc⟩ := hA
  let v : AM.M₀.E := ∑ i, β i • (D.bV AM i : AM.M₀.E)
  have hvne : v ≠ 0 := bV_sum_ne_zero D AM hβ
  have hspan : D.Bsp AM = AM.K ∙ v :=
    eq_span_singleton_of_mem_of_finrank_eq_one (D.finrank_Bsp AM) hβB hvne
  have hphi : AM.φ ⟨r, D.Rt_le_H0 hrR⟩ v = c • v :=
    phi_bV_sum_eq_smul D AM hrR hc
  intro w hw
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hw)
  rw [map_smul, hphi, smul_smul]
  exact Submodule.smul_mem _ _ hβB

private theorem mem_normalizer_of_piM_mem_normalizer (hc : Ctx M Q Z B) {L : Subgroup G}
    (hQL : Q ≤ L) (hLM : L ≤ M) {r : G} (hrM : r ∈ M)
    (hr : HS6.piM M Q r ∈ Subgroup.normalizer (bar M Q L : Set (Mbar M Q))) :
    r ∈ Subgroup.normalizer (L : Set G) := by
  obtain ⟨h, hhM, hpi, hhN⟩ := HS6.exists_lift_normalizer (hc.hyp.Q_normal.1)
    (fun x hx k hk => (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hk) x).mp hx)
    hQL hLM hr
  have hq : h⁻¹ * r ∈ Q := (HS6.piM_eq_iff hhM hrM).mp hpi
  have hqL : h⁻¹ * r ∈ L := hQL hq
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hx' : (h⁻¹ * r) * x * (h⁻¹ * r)⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem hqL hx) (L.inv_mem hqL)
  have hhN' : h ∈ Subgroup.normalizer (L : Set G) := conjSubgroup_eq_self_iff.mp hhN
  have hconj : h * ((h⁻¹ * r) * x * (h⁻¹ * r)⁻¹) * h⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hhN' _).mp hx'
  rwa [show r * x * r⁻¹ = h * ((h⁻¹ * r) * x * (h⁻¹ * r)⁻¹) * h⁻¹ by group]

private theorem mem_normalizer_bar_LB_iff_mem_normalizer_sup
    (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z) {r : G}
    (hrR : r ∈ Rt M (LB M Q B) t) :
    HS6.piM M Q r ∈ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) ↔
      r ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) := by
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  constructor
  · intro h
    exact (stroth_11_1a hc D.hyp.width (by norm_num) hrM).mpr
      (mem_normalizer_of_piM_mem_normalizer hc le_sup_left hc.LB_le_M hrM h)
  · intro h
    exact HS6.piM_mem_normalizer (hc.hyp.Q_normal.1) hrM
      (conjSubgroup_eq_self_iff.mpr ((stroth_11_1a hc D.hyp.width (by norm_num) hrM).mp h))

private theorem matV_mulVec_smul_iff_mem_normalizer_sup {r : G}
    (hrR : r ∈ Rt M (LB M Q B) t) {β : Fin 3 → AM.K} (hβ : β ≠ 0)
    (hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM) :
    (∃ c : AM.K, D.matV AM ⟨r, D.Rt_le_H0 hrR⟩ *ᵥ β = c • β) ↔
      r ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) := by
  constructor
  · rintro ⟨c, hc⟩
    exact mem_normalizer_sup_of_maps_Bsp D AM (D.Rt_le_H0 hrR)
      (maps_Bsp_of_matV_mulVec_eq_smul D AM hrR hβ hβB ⟨c, hc⟩)
  · intro hN
    exact matV_mulVec_eq_smul_of_maps_Bsp D AM (D.Rt_le_H0 hrR) hβ hβB
      (maps_Bsp_of_mem_normalizer_sup D AM (D.Rt_le_H0 hrR) hN)

private theorem rhoMat_eq_frame {r : G} (hrR : r ∈ Rt M (LB M Q B) t) :
    (D.rhoMat AM ⟨r, hrR⟩ : Matrix (Fin 3) (Fin 3) AM.K) =
      (((D.frameB AM)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) AM.K) :
        Matrix (Fin 3) (Fin 3) AM.K) * D.matV AM ⟨r, D.Rt_le_H0 hrR⟩ *
        (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) := rfl

private theorem rhoMat_entries_of_matV_mulVec_smul {r : G}
    (hrR : r ∈ Rt M (LB M Q B) t) {c : AM.K}
    (hA : D.matV AM ⟨r, D.Rt_le_H0 hrR⟩ *ᵥ
      ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ Sec108.e₀ AM.K) = c •
      ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ Sec108.e₀ AM.K)) :
    (D.rhoMat AM ⟨r, hrR⟩) 1 0 = 0 ∧ (D.rhoMat AM ⟨r, hrR⟩) 2 0 = 0 := by
  let P : Matrix.SpecialLinearGroup (Fin 3) AM.K := D.frameB AM
  rw [rhoMat_eq_frame D AM hrR]
  have hRho := frame_mulVec_e0_of_mulVec_beta P hA
  rw [mulVec_e0_eq_col] at hRho
  constructor
  · have h := congrFun hRho 1
    simpa [Sec108.e₀, Matrix.col_apply] using h
  · have h := congrFun hRho 2
    simpa [Sec108.e₀, Matrix.col_apply] using h

private theorem matV_mulVec_smul_of_rhoMat_entries {r : G}
    (hrR : r ∈ Rt M (LB M Q B) t)
    (h10 : (D.rhoMat AM ⟨r, hrR⟩) 1 0 = 0)
    (h20 : (D.rhoMat AM ⟨r, hrR⟩) 2 0 = 0) :
    ∃ c : AM.K, D.matV AM ⟨r, D.Rt_le_H0 hrR⟩ *ᵥ
      ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ Sec108.e₀ AM.K) = c •
      ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ Sec108.e₀ AM.K) := by
  let P : Matrix.SpecialLinearGroup (Fin 3) AM.K := D.frameB AM
  let A : Matrix (Fin 3) (Fin 3) AM.K :=
    (((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) AM.K) : Matrix (Fin 3) (Fin 3) AM.K) *
      D.matV AM ⟨r, D.Rt_le_H0 hrR⟩ * (P : Matrix (Fin 3) (Fin 3) AM.K))
  have hA : (D.rhoMat AM ⟨r, hrR⟩ : Matrix (Fin 3) (Fin 3) AM.K) = A :=
    rhoMat_eq_frame D AM hrR
  have h10' : A 1 0 = 0 := by rw [← hA]; exact h10
  have h20' : A 2 0 = 0 := by rw [← hA]; exact h20
  let c : AM.K := A 0 0
  have hRho : A *ᵥ Sec108.e₀ AM.K = c • Sec108.e₀ AM.K := by
    rw [mulVec_e0_eq_col]
    ext i
    fin_cases i
    · simp [Sec108.e₀, Matrix.col_apply, c]
    · simpa [A, h10'] using h10'
    · simpa [A, h20'] using h20'
  exact ⟨c, mulVec_beta_of_frame_mulVec_e0 P hRho⟩

private theorem matV_mulVec_smul_iff_rhoMat_entries {r : G}
    (hrR : r ∈ Rt M (LB M Q B) t) :
    (∃ c : AM.K, D.matV AM ⟨r, D.Rt_le_H0 hrR⟩ *ᵥ
        ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ Sec108.e₀ AM.K) = c •
        ((D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ Sec108.e₀ AM.K)) ↔
      (D.rhoMat AM ⟨r, hrR⟩) 1 0 = 0 ∧ (D.rhoMat AM ⟨r, hrR⟩) 2 0 = 0 :=
  ⟨fun ⟨_, hA⟩ => rhoMat_entries_of_matV_mulVec_smul D AM hrR hA,
    fun ⟨h10, h20⟩ => matV_mulVec_smul_of_rhoMat_entries D AM hrR h10 h20⟩

theorem Sec108Data.mem_normalizer_bar_LB_iff (r : Mbar M Q)
    (hr : r ∈ bar M Q (Rt M (LB M Q B) t)) :
    r ∈ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) ↔
      ((D.rho AM ⟨r, hr⟩ : GL (Fin 3) AM.K) : Matrix (Fin 3) (Fin 3) AM.K) 1 0 = 0 ∧
        ((D.rho AM ⟨r, hr⟩ : GL (Fin 3) AM.K) : Matrix (Fin 3) (Fin 3) AM.K) 2 0 = 0 := by
  obtain ⟨r₀, hr₀R, hr₀M, hpi⟩ := (HS6.mem_bar r).mp hr
  subst r
  let β : Fin 3 → AM.K := (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ Sec108.e₀ AM.K
  have hβ : β ≠ 0 := frameB_mulVec_e0_ne_zero D AM
  have hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM := D.frameB_mem_Bsp AM
  have hrho := D.rho_piM AM hr₀R hr
  rw [hrho]
  exact (mem_normalizer_bar_LB_iff_mem_normalizer_sup D AM hr₀R).trans
    ((matV_mulVec_smul_iff_mem_normalizer_sup D AM hr₀R hβ hβB).symm.trans
      (matV_mulVec_smul_iff_rhoMat_entries D AM hr₀R))

end CFSG.RankThree.GF2n.Stroth80
