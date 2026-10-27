module

public import CFSG.Quasithin.Vol2.Ch9Sec3Conj

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H CFSG.Quasithin.E3 Matrix

namespace Om4Pt

variable {K : Type} [Field K]

theorem coe_toGL_uHom (c : K) :
    ((Matrix.SpecialLinearGroup.toGL (uHom K (Multiplicative.ofAdd c)) : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := rfl

theorem lr_eq_of_smul {A B A' B' : GL (Fin 2) K} {c : K} (hc : c ≠ 0)
    (hA : (A' : Matrix (Fin 2) (Fin 2) K) = c • (A : Matrix (Fin 2) (Fin 2) K))
    (hB : (B' : Matrix (Fin 2) (Fin 2) K) = c⁻¹ • (B : Matrix (Fin 2) (Fin 2) K)) :
    Om4.lr A' B' = Om4.lr A B := by
  refine MulEquiv.ext fun X => Multiplicative.toAdd.injective ?_
  rw [Om4.toAdd_lr, Om4.toAdd_lr, hA, hB]
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

theorem eq_of_sq_eq_sq [CharP K 2] {a b : K} (h : a ^ 2 = b ^ 2) : a = b := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : (a - b) ^ 2 = 0 := by linear_combination h + (b ^ 2 - a * b) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)

theorem exists_rho_of_sq [CharP K 2] {A B : GL (Fin 2) K} (hA : Om4.IsUT A) (hB : Om4.IsUT B)
    (hAB : (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 0 0 = 1)
    (h2 : Om4.lr A B * Om4.lr A B = 1) :
    ∃ x y : K, Om4.lr A B =
      Om4.rho (uHom K (Multiplicative.ofAdd x), uHom K (Multiplicative.ofAdd y)) := by
  rw [Om4.lr_mul] at h2
  obtain ⟨c, -, hA2, hB2⟩ := Om4.exists_smul_of_lr_eq_one h2
  have hA0 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hAB
  have eA : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = (A : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    have e00 := congrFun (congrFun hA2 0) 0
    have e11 := congrFun (congrFun hA2 1) 1
    rw [← pow_two, hA.pow_apply_zero_zero] at e00
    rw [← pow_two, hA.pow_apply_one_one] at e11
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e00 e11
    exact eq_of_sq_eq_sq (e11.trans e00.symm)
  have eB : (B : Matrix (Fin 2) (Fin 2) K) 1 1 = (B : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    have e00 := congrFun (congrFun hB2 0) 0
    have e11 := congrFun (congrFun hB2 1) 1
    rw [← pow_two, hB.pow_apply_zero_zero] at e00
    rw [← pow_two, hB.pow_apply_one_one] at e11
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e00 e11
    exact eq_of_sq_eq_sq (e11.trans e00.symm)
  set a := (A : Matrix (Fin 2) (Fin 2) K) 0 0 with ha
  refine ⟨a⁻¹ * (A : Matrix (Fin 2) (Fin 2) K) 0 1, a * (B : Matrix (Fin 2) (Fin 2) K) 0 1, ?_⟩
  rw [Om4.rho_apply]
  symm
  refine lr_eq_of_smul (inv_ne_zero hA0) ?_ ?_
  · rw [coe_toGL_uHom]
    unfold Om4.IsUT at hA
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA, eA, ← ha, inv_mul_cancel₀ hA0]
  · rw [coe_toGL_uHom, inv_inv]
    unfold Om4.IsUT at hB
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hB, eB, hAB]

theorem eq_inv_of_sq_swap [CharP K 2] {A B : GL (Fin 2) K}
    (h2 : Om4.lr A B * Om4.trM * (Om4.lr A B * Om4.trM) = 1) : B = A⁻¹ := by
  have e1 : Om4.lr A B * Om4.trM * (Om4.lr A B * Om4.trM) = Om4.lr (A * B) (B * A) := by
    calc Om4.lr A B * Om4.trM * (Om4.lr A B * Om4.trM)
        = Om4.lr A B * (Om4.trM * Om4.lr A B) * Om4.trM := by group
      _ = Om4.lr A B * Om4.lr B A * (Om4.trM * Om4.trM) := by rw [Om4.trM_lr]; group
      _ = _ := by rw [Om4.trM_mul_self, mul_one, Om4.lr_mul]
  rw [e1] at h2
  obtain ⟨c, hc, h1, h3⟩ := Om4.exists_smul_of_lr_eq_one h2
  have hBA : ((B * A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = c • 1 := by
    have hB : (B : Matrix (Fin 2) (Fin 2) K) =
        c • ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      have : (B : Matrix (Fin 2) (Fin 2) K) = ((A⁻¹ * (A * B) : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) := by rw [inv_mul_cancel_left]
      rw [this, Units.val_mul, h1, Matrix.mul_smul, Matrix.mul_one]
    rw [Units.val_mul, hB, Matrix.smul_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcc : c = c⁻¹ := by
    have := congrFun (congrFun (hBA.symm.trans h3) 0) 0
    simpa using this
  have hc1 : c = 1 := by
    have h4 : c ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [hcc]
      exact mul_inv_cancel₀ hc
    exact eq_of_sq_eq_sq (h4.trans (one_pow 2).symm)
  rw [hc1, one_smul] at h1
  have h5 : A * B = 1 := Units.ext (by rw [h1, Units.val_one])
  exact eq_inv_of_mul_eq_one_right h5

theorem not_isNS_lr_trM (A B : GL (Fin 2) K) : ¬ Om4.IsNS (Om4.lr A B * Om4.trM) := by
  intro h
  apply Om4.not_isNS_trM (K := K)
  have h1 : Om4.IsNS (Om4.lr A B) := ⟨A, B, 1, by rw [Om4.frM_one, mul_one]⟩
  have := h1.inv.mul h
  rwa [← mul_assoc, inv_mul_cancel, one_mul] at this

theorem toAdd_rho_e21 (x y : K) :
    Multiplicative.toAdd (Om4.rho (uHom K (Multiplicative.ofAdd x),
      uHom K (Multiplicative.ofAdd y)) (Multiplicative.ofAdd !![0, 0; 1, 0])) =
        !![x, 0; 1, 0] := by
  rw [toAdd_rho, toAdd_ofAdd, coe_uHom, coe_uHom]
  ext i j
  rw [mul_mul_transpose_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem toAdd_rho_e12 (x y : K) :
    Multiplicative.toAdd (Om4.rho (uHom K (Multiplicative.ofAdd x),
      uHom K (Multiplicative.ofAdd y)) (Multiplicative.ofAdd !![0, 1; 0, 0])) =
        !![y, 1; 0, 0] := by
  rw [toAdd_rho, toAdd_ofAdd, coe_uHom, coe_uHom]
  ext i j
  rw [mul_mul_transpose_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem rho_uHom_zero :
    Om4.rho (uHom K (Multiplicative.ofAdd (0 : K)), uHom K (Multiplicative.ofAdd (0 : K))) = 1 := by
  rw [ofAdd_zero, map_one, ← Prod.one_eq_mk, map_one]

theorem mul_eq_of_commute_swap {x y : K} {P : GL (Fin 2) K} (hP : Om4.IsUT P)
    (h : Om4.rho (uHom K (Multiplicative.ofAdd x), uHom K (Multiplicative.ofAdd y)) *
        (Om4.lr P P⁻¹ * Om4.trM) = (Om4.lr P P⁻¹ * Om4.trM) *
          Om4.rho (uHom K (Multiplicative.ofAdd x), uHom K (Multiplicative.ofAdd y))) :
    x * (P : Matrix (Fin 2) (Fin 2) K) 1 1 = (P : Matrix (Fin 2) (Fin 2) K) 0 0 * y := by
  set U := Matrix.SpecialLinearGroup.toGL (uHom K (Multiplicative.ofAdd x)) with hU
  set W := Matrix.SpecialLinearGroup.toGL (uHom K (Multiplicative.ofAdd y)) with hW
  rw [Om4.rho_apply] at h
  change Om4.lr U W * (Om4.lr P P⁻¹ * Om4.trM) = (Om4.lr P P⁻¹ * Om4.trM) * Om4.lr U W at h
  have e1 : Om4.lr U W * (Om4.lr P P⁻¹ * Om4.trM) = Om4.lr (U * P) (W * P⁻¹) * Om4.trM := by
    rw [← mul_assoc, Om4.lr_mul]
  have e2 : (Om4.lr P P⁻¹ * Om4.trM) * Om4.lr U W = Om4.lr (P * W) (P⁻¹ * U) * Om4.trM := by
    rw [mul_assoc, Om4.trM_lr, ← mul_assoc, Om4.lr_mul]
  rw [e1, e2] at h
  obtain ⟨c, -, h1, -⟩ := Om4.exists_smul_of_lr_eq (mul_right_cancel h)
  have hP11 := hP.apply_ne_zero.2
  unfold Om4.IsUT at hP
  have e11 := congrFun (congrFun h1 1) 1
  have e01 := congrFun (congrFun h1 0) 1
  rw [Units.val_mul, Units.val_mul, hU, hW, coe_toGL_uHom, coe_toGL_uHom] at e11 e01
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, hP] at e11 e01
  simp at e11 e01
  have hc : c = 1 := by
    have : (1 - c) * (P : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by linear_combination e11
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hP11)).symm
  rw [hc, one_mul] at e01
  linear_combination -e01

theorem swap_smul_e11 {P : GL (Fin 2) K} (hP : Om4.IsUT P) (c : K) :
    (Om4.lr P P⁻¹ * Om4.trM : MulAut (Om4.VM K)) (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
      Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0]) := by
  obtain ⟨hPi, hPi0, -⟩ := hP.inv
  have hP0 := hP.apply_ne_zero.1
  apply Multiplicative.toAdd.injective
  rw [MulAut.mul_apply, Om4.trM_smul_e11, Om4.toAdd_lr, toAdd_ofAdd]
  unfold Om4.IsUT at hP hPi
  ext i j
  rw [mul_mul_transpose_apply]
  fin_cases i <;> fin_cases j <;> simp [hP, hPi, hPi0]
  rw [mul_left_comm, mul_inv_cancel₀ hP0, mul_one]

theorem swap_mul_e22 (P : GL (Fin 2) K) :
    (Om4.lr P P⁻¹ * Om4.trM : MulAut (Om4.VM K)) (Multiplicative.ofAdd
      ((P : Matrix (Fin 2) (Fin 2) K) * !![0, 0; 0, 1])) =
        Multiplicative.ofAdd ((P : Matrix (Fin 2) (Fin 2) K) * !![0, 0; 0, 1]) := by
  apply Multiplicative.toAdd.injective
  have hPP : (P : Matrix (Fin 2) (Fin 2) K)ᵀ * ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ =
      1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]
  rw [MulAut.mul_apply, Om4.toAdd_lr, Om4.toAdd_trM, toAdd_ofAdd, Matrix.transpose_mul,
    Matrix.mul_assoc, Matrix.mul_assoc, hPP, Matrix.mul_one]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem swap_e12_apply_ne_zero {P : GL (Fin 2) K} (hP : Om4.IsUT P) :
    Multiplicative.toAdd ((Om4.lr P P⁻¹ * Om4.trM : MulAut (Om4.VM K))
      (Multiplicative.ofAdd !![0, 1; 0, 0])) 1 0 ≠ 0 := by
  obtain ⟨hPi, hPi0, -⟩ := hP.inv
  obtain ⟨hP0, hP1⟩ := hP.apply_ne_zero
  rw [MulAut.mul_apply, Om4.toAdd_lr, Om4.toAdd_trM, toAdd_ofAdd, mul_mul_transpose_apply]
  unfold Om4.IsUT at hP hPi
  simp [hP, hPi0, hP0, hP1]

@[expose] def dMat (P : Matrix (Fin 2) (Fin 2) K) (y : K) : Matrix (Fin 2) (Fin 2) K :=
  !![y * (P 0 1 + P 0 0 * y), P 0 0 * y; P 1 1 * y, 0]

theorem toAdd_rho_mul_e22 {x y : K} {P : GL (Fin 2) K} (hP : Om4.IsUT P)
    (hxy : x * (P : Matrix (Fin 2) (Fin 2) K) 1 1 = (P : Matrix (Fin 2) (Fin 2) K) 0 0 * y) :
    Multiplicative.toAdd (Om4.rho (uHom K (Multiplicative.ofAdd x),
      uHom K (Multiplicative.ofAdd y)) (Multiplicative.ofAdd ((P : Matrix (Fin 2) (Fin 2) K) *
        !![0, 0; 0, 1]))) = (P : Matrix (Fin 2) (Fin 2) K) * !![0, 0; 0, 1] +
          dMat (P : Matrix (Fin 2) (Fin 2) K) y := by
  rw [toAdd_rho, toAdd_ofAdd, coe_uHom, coe_uHom]
  unfold Om4.IsUT at hP
  ext i j
  rw [mul_mul_transpose_apply]
  fin_cases i <;> fin_cases j <;> simp [dMat, Matrix.mul_apply, Fin.sum_univ_two, hP] <;>
    first | linear_combination y * hxy | linear_combination hxy

theorem det_dMat_ne_zero {P : GL (Fin 2) K} (hP : Om4.IsUT P) {y : K} (hy : y ≠ 0) :
    (dMat (P : Matrix (Fin 2) (Fin 2) K) y).det ≠ 0 := by
  obtain ⟨hP0, hP1⟩ := hP.apply_ne_zero
  rw [dMat, Matrix.det_fin_two_of]
  simp only [mul_zero, zero_sub, neg_ne_zero]
  exact mul_ne_zero (mul_ne_zero hP0 hy) (mul_ne_zero hP1 hy)

theorem dMat_ne_smul {P : GL (Fin 2) K} (hP : Om4.IsUT P) {y₁ y₂ : K} (hy₁ : y₁ ≠ 0)
    (hy₂ : y₂ ≠ 0) (hne : y₂ ≠ y₁) (c : K) :
    dMat (P : Matrix (Fin 2) (Fin 2) K) y₂ ≠ c • dMat (P : Matrix (Fin 2) (Fin 2) K) y₁ := by
  intro h
  obtain ⟨hP0, hP1⟩ := hP.apply_ne_zero
  have d10 : ∀ y, dMat (P : Matrix (Fin 2) (Fin 2) K) y 1 0 =
      (P : Matrix (Fin 2) (Fin 2) K) 1 1 * y := fun y => rfl
  have d00 : ∀ y, dMat (P : Matrix (Fin 2) (Fin 2) K) y 0 0 =
      y * ((P : Matrix (Fin 2) (Fin 2) K) 0 1 + (P : Matrix (Fin 2) (Fin 2) K) 0 0 * y) :=
    fun y => rfl
  have e10 := congrFun (congrFun h 1) 0
  have e00 := congrFun (congrFun h 0) 0
  rw [Matrix.smul_apply, smul_eq_mul, d10, d10] at e10
  rw [Matrix.smul_apply, smul_eq_mul, d00, d00] at e00
  have h1 : y₂ = c * y₁ := by
    have : (P : Matrix (Fin 2) (Fin 2) K) 1 1 * (y₂ - c * y₁) = 0 := by linear_combination e10
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hP1)
  rw [h1] at e00
  have h2 : ((P : Matrix (Fin 2) (Fin 2) K) 0 0 * y₁ * y₁) * (c * (c - 1)) = 0 := by
    linear_combination e00
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hy₂ (by rw [h1, zero_mul])
  have hc : c = 1 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (mul_ne_zero (mul_ne_zero hP0 hy₁) hy₁)
    · exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hc0)
  exact hne (by rw [h1, hc, one_mul])

end Om4Pt

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem conj_symm {K : Type} [Field K] (e : ↥(fsuV T I) ≃* Om4.VM K)
    (x : ↥(Subgroup.normalizer (fsuV T I : Set G))) (Y : Om4.VM K) :
    (x : G) * (e.symm Y : G) * (x : G)⁻¹ = (e.symm (bar e x Y) : G) := by
  have h := bar_apply e x (e.symm Y)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, MulEquiv.symm_apply_apply]

omit [Finite G] in
theorem e_comm_symm {K : Type} [Field K] (e : ↥(fsuV T I) ≃* Om4.VM K)
    (x : ↥(Subgroup.normalizer (fsuV T I : Set G))) (Y : Om4.VM K)
    (h : (e.symm Y : G) * x * (e.symm Y : G)⁻¹ * (x : G)⁻¹ ∈ fsuV T I) :
    e ⟨(e.symm Y : G) * x * (e.symm Y : G)⁻¹ * (x : G)⁻¹, h⟩ = Y * (bar e x Y)⁻¹ := by
  have e1 : (e.symm Y : G) * x * (e.symm Y : G)⁻¹ * (x : G)⁻¹ =
      ((e.symm (Y * (bar e x Y)⁻¹) : ↥(fsuV T I)) : G) := by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, ← conj_symm e x Y]
    group
  have e2 : (⟨(e.symm Y : G) * x * (e.symm Y : G)⁻¹ * (x : G)⁻¹, h⟩ : ↥(fsuV T I)) =
      e.symm (Y * (bar e x Y)⁻¹) := Subtype.ext e1
  rw [e2, MulEquiv.apply_symm_apply]

omit [Finite G] in
theorem comm_symm_mem {K : Type} [Field K] (e : ↥(fsuV T I) ≃* Om4.VM K)
    (x : ↥(Subgroup.normalizer (fsuV T I : Set G))) (Y : Om4.VM K) :
    (e.symm Y : G) * x * (e.symm Y : G)⁻¹ * (x : G)⁻¹ ∈ fsuV T I := by
  have : (e.symm Y : G) * x * (e.symm Y : G)⁻¹ * (x : G)⁻¹ =
      (e.symm Y : G) * ((x : G) * (e.symm Y : G) * (x : G)⁻¹)⁻¹ := by group
  rw [this, conj_symm]
  exact (fsuV T I).mul_mem (e.symm Y).2 ((fsuV T I).inv_mem (e.symm _).2)

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem form_of_mem_centralizer_V1 {a : G} (haT : a ∈ T)
    (haV1 : a ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G)) (ha2 : a ^ 2 = 1) :
    (∃ x y : K, bar e ⟨a, S.hMN (Setup.T_le_fsuM haT)⟩ =
      Om4.rho (uHom K (Multiplicative.ofAdd x), uHom K (Multiplicative.ofAdd y))) ∨
    ∃ P : GL (Fin 2) K, Om4.IsUT P ∧
      bar e ⟨a, S.hMN (Setup.T_le_fsuM haT)⟩ = Om4.lr P P⁻¹ * Om4.trM := by
  set φ := bar e ⟨a, S.hMN (Setup.T_le_fsuM haT)⟩ with hφ
  obtain ⟨A, B, τ, hA, hB, hform⟩ := hc.exists_form_ut haT
  rw [← hφ] at hform
  have hfix : ∀ c : K, φ (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
      Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0]) := by
    intro c
    have hw := hc.symm_mem c
    have h1 := conj_symm e ⟨a, S.hMN (Setup.T_le_fsuM haT)⟩
      (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0]))
    have h2 : a * ((e.symm (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) : ↥(fsuV T I)) : G) *
        a⁻¹ = ((e.symm (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) : ↥(fsuV T I)) : G) := by
      rw [(Subgroup.mem_centralizer_iff.mp haV1 _ hw).symm, mul_inv_cancel_right]
    rw [h2] at h1
    exact (e.symm.injective (Subtype.ext h1)).symm
  have hscal : ∀ c : K, (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 0 0 *
      τ c = c := by
    intro c
    have h1 := hfix c
    have h2 : φ (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
        (Om4.lr A B * Om4.frM τ) (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) := by
      rcases hform with h | h
      · rw [h]
      · rw [h, MulAut.mul_apply, Om4.trM_smul_e11]
    rw [h2, Om4.apply_smul_e11 hA hB] at h1
    have h3 := congrArg (fun X : Om4.VM K => Multiplicative.toAdd X 0 0) h1
    have e11 : (!![(1 : K), 0; 0, 0] : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := rfl
    simp only [toAdd_ofAdd, Matrix.smul_apply, smul_eq_mul, e11, mul_one] at h3
    exact h3
  have hAB : (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    simpa using hscal 1
  have hτ : τ = 1 := by
    ext c
    have := hscal c
    rw [hAB, one_mul] at this
    exact this
  rw [hτ, Om4.frM_one, mul_one] at hform
  have hφ2 : φ * φ = 1 := by
    rw [hφ, ← map_mul]
    have : (⟨a, S.hMN (Setup.T_le_fsuM haT)⟩ : ↥(Subgroup.normalizer (fsuV T I : Set G))) *
        ⟨a, S.hMN (Setup.T_le_fsuM haT)⟩ = 1 := Subtype.ext (by
          rw [Subgroup.coe_mul, ← pow_two, ha2]; rfl)
    rw [this, map_one]
  rcases hform with h | h
  · left
    rw [h] at hφ2 ⊢
    exact Om4Pt.exists_rho_of_sq hA hB hAB hφ2
  · right
    rw [h] at hφ2 ⊢
    refine ⟨A, hA, ?_⟩
    rw [Om4Pt.eq_inv_of_sq_swap hφ2]

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
