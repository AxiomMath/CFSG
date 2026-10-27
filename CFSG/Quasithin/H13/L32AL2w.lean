module

public import CFSG.Quasithin.H13.L32AL2v

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Quasithin.H.Om4 Matrix

variable {F : Type} [Field F]

theorem ut_mul_entries {M N : Matrix (Fin 2) (Fin 2) F} (hM : M 1 0 = 0) (hN : N 1 0 = 0) :
    (M * N) 1 0 = 0 ∧ (M * N) 0 0 = M 0 0 * N 0 0 ∧ (M * N) 1 1 = M 1 1 * N 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, hM, hN]

theorem ut_inv_entries {A : GL (Fin 2) F} (hA : IsUT A) :
    ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (A : Matrix (Fin 2) (Fin 2) F) 0 0 * ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        1 ∧
      (A : Matrix (Fin 2) (Fin 2) F) 1 1 * ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
        1 := by
  have h1 : (A : Matrix (Fin 2) (Fin 2) F) * ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨h00, h11⟩ := hA.apply_ne_zero
  have hA' : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hA
  have hB : ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have e10 := congrFun (congrFun h1 1) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, hA', zero_mul, zero_add,
      Matrix.one_apply_ne (by decide)] at e10
    exact (mul_eq_zero.mp e10).resolve_left h11
  refine ⟨hB, ?_, ?_⟩
  · have e00 := congrFun (congrFun h1 0) 0
    rwa [Matrix.mul_apply, Fin.sum_univ_two, hB, mul_zero, add_zero, Matrix.one_apply_eq] at e00
  · have e11 := congrFun (congrFun h1 1) 1
    rwa [Matrix.mul_apply, Fin.sum_univ_two, hA', zero_mul, zero_add, Matrix.one_apply_eq] at e11

theorem sl_ut_det {g : SpecialLinearGroup (Fin 2) F} (hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
  have := g.2
  rw [Matrix.det_fin_two, hg, mul_zero, sub_zero] at this
  exact this

theorem conj_utS {g : SpecialLinearGroup (Fin 2) F} (hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (x : F) : g * utS x * g⁻¹ = utS ((g : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * x) := by
  have hd := sl_ut_det hg
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  fin_cases i <;> fin_cases j <;>
    simp [utS, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, hg]
  · linear_combination hd
  · ring
  · linear_combination hd

theorem borel_conj_sZero {g h : SpecialLinearGroup (Fin 2) F}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (hh : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (p q : F) :
    rho (g, h) * rho (utS p, utS q) * (rho (g, h))⁻¹ =
      rho (utS ((g : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * p),
        utS ((h : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * q)) := by
  rw [← map_inv, ← map_mul, ← map_mul, Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, conj_utS hg,
    conj_utS hh]

theorem comm_iff [CharP F 2] (A : GL (Fin 2) F) (g h : SpecialLinearGroup (Fin 2) F) :
    rho (g, h) * (lr A A⁻¹ * trM) = (lr A A⁻¹ * trM) * rho (g, h) ↔
      (h : Matrix (Fin 2) (Fin 2) F) = ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (g : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set G := Matrix.SpecialLinearGroup.toGL g with hG
  set H := Matrix.SpecialLinearGroup.toGL h with hH
  have e1 : rho (g, h) * (lr A A⁻¹ * trM) = lr (G * A) (H * A⁻¹) * trM := by
    rw [rho_apply, ← mul_assoc, lr_mul]
  have e2 : (lr A A⁻¹ * trM) * rho (g, h) = lr (A * H) (A⁻¹ * G) * trM := by
    rw [rho_apply, mul_assoc, trM_lr, ← mul_assoc, lr_mul]
  rw [e1, e2, mul_left_inj]
  constructor
  · intro e
    have e3 : lr ((A * H)⁻¹ * (G * A)) ((A⁻¹ * G)⁻¹ * (H * A⁻¹)) = 1 := by
      rw [← lr_mul, e, lr_mul, inv_mul_cancel, inv_mul_cancel, lr_one]
    obtain ⟨c, hc, -⟩ := exists_smul_of_lr_eq_one e3
    have hdet : (((A * H)⁻¹ * (G * A) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      have hG1 : Matrix.GeneralLinearGroup.det G = 1 := Units.ext g.2
      have hH1 : Matrix.GeneralLinearGroup.det H = 1 := Units.ext h.2
      have : Matrix.GeneralLinearGroup.det ((A * H)⁻¹ * (G * A)) = 1 := by
        simp only [map_mul, map_inv, hG1, hH1, mul_one, one_mul]
        exact inv_mul_cancel _
      have := congrArg Units.val this
      rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
    rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    have hc1 : c = 1 := by
      have h3 : (c + 1) * (c + 1) = 0 := by linear_combination hdet + (c + 1) * h2
      linear_combination mul_self_eq_zero.mp h3 - h2
    rw [hc1, one_smul] at hc
    have e4 : (A * H)⁻¹ * (G * A) = 1 := Units.ext hc
    have e4' : A * H = G * A := inv_mul_eq_one.mp e4
    have e5 : H = A⁻¹ * G * A := by
      calc H = A⁻¹ * (A * H) := by group
        _ = A⁻¹ * G * A := by rw [e4', mul_assoc]
    have := congrArg Units.val e5
    rwa [Units.val_mul, Units.val_mul] at this
  · intro e
    have e5 : H = A⁻¹ * G * A := Units.ext (by rw [Units.val_mul, Units.val_mul]; exact e)
    rw [e5]
    congr 1 <;> group

theorem eq_one_of_actsSmul_mem_range [CharP F 2] {z : MulAut (VM F)} {e : F} (hz : ActsSmul z e)
    (h : z ∈ (rho (K := F)).range) : e = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨⟨g, k⟩, hgk⟩ := h
  have key : ∀ X : Matrix (Fin 2) (Fin 2) F,
      (g : Matrix (Fin 2) (Fin 2) F) * X * (k : Matrix (Fin 2) (Fin 2) F)ᵀ = e • X := by
    intro X
    rw [← hz X, ← hgk, rho_apply, toAdd_lr, toAdd_ofAdd]
    rfl
  have hk : (k : Matrix (Fin 2) (Fin 2) F)ᵀ = e • ((g⁻¹ : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) := by
    have h1 := key 1
    rw [Matrix.mul_one] at h1
    calc (k : Matrix (Fin 2) (Fin 2) F)ᵀ
        = ((g⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((g : Matrix (Fin 2) (Fin 2) F) * (k : Matrix (Fin 2) (Fin 2) F)ᵀ) := by
          rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
            Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
      _ = _ := by rw [h1, Matrix.mul_smul, Matrix.mul_one]
  have hdet := congrArg Matrix.det hk
  rw [Matrix.det_transpose, k.2, Matrix.det_smul, (g⁻¹).2, mul_one, Fintype.card_fin] at hdet
  have h3 : (e + 1) * (e + 1) = 0 := by linear_combination -hdet + (e + 1) * h2
  linear_combination mul_self_eq_zero.mp h3 - h2

theorem sq_sq_eq [Finite F] (h4 : Nat.card F = 4) (c : F) : (c ^ 2) ^ 2 = c := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, h4]
  have := FiniteField.pow_card c
  rw [hcard] at this
  rw [← pow_mul]
  exact this

theorem smul_mul_smul_mul_transpose (r s u : F) (M N Z : Matrix (Fin 2) (Fin 2) F) :
    (r • M) * (s • N) * (u • Z)ᵀ = (r * s * u) • (M * N * Zᵀ) := by
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  ring

theorem mem_range_of_pow [Finite F] [CharP F 2] (h4 : Nat.card F = 4) {P Q : GL (Fin 2) F}
    {k : ℕ} (hk : (lr P Q) ^ (2 ^ k) = 1) : lr P Q ∈ (rho (K := F)).range := by
  set p : F := (P : Matrix (Fin 2) (Fin 2) F).det with hp
  set q : F := (Q : Matrix (Fin 2) (Fin 2) F).det with hq
  have hp0 : p ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp P.isUnit).ne_zero
  have hq0 : q ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp Q.isUnit).ne_zero
  have hμ0 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp0
  have hν0 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq0
  have hdP : ((p ^ 2)⁻¹ • (P : Matrix (Fin 2) (Fin 2) F)).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, ← hp, inv_pow, sq_sq_eq h4, inv_mul_cancel₀ hp0]
  have hdQ : ((q ^ 2)⁻¹ • (Q : Matrix (Fin 2) (Fin 2) F)).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, ← hq, inv_pow, sq_sq_eq h4, inv_mul_cancel₀ hq0]
  set P' : SpecialLinearGroup (Fin 2) F := ⟨_, hdP⟩ with hP'
  set Q' : SpecialLinearGroup (Fin 2) F := ⟨_, hdQ⟩ with hQ'
  set e : F := p ^ 2 * q ^ 2 with he
  set z := smulM e (mul_ne_zero hμ0 hν0) with hz
  have hzs : ActsSmul z e := fun X => rfl
  have hsplit : lr P Q = rho (P', Q') * z := by
    refine MulEquiv.ext fun X => Multiplicative.toAdd.injective ?_
    rw [MulAut.mul_apply, rho_apply, toAdd_lr, toAdd_lr, hz, toAdd_smulM]
    change (P : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd X *
        (Q : Matrix (Fin 2) (Fin 2) F)ᵀ =
      ((p ^ 2)⁻¹ • (P : Matrix (Fin 2) (Fin 2) F)) * (e • Multiplicative.toAdd X) *
        ((q ^ 2)⁻¹ • (Q : Matrix (Fin 2) (Fin 2) F))ᵀ
    rw [smul_mul_smul_mul_transpose, show (p ^ 2)⁻¹ * e * (q ^ 2)⁻¹ = 1 by
      rw [he]; field_simp, one_smul]
  have hcomm : Commute (rho (P', Q')) z := by
    refine MulEquiv.ext fun X => Multiplicative.toAdd.injective ?_
    rw [MulAut.mul_apply, MulAut.mul_apply, rho_apply, toAdd_lr, hz, toAdd_smulM, toAdd_smulM,
      toAdd_lr, Matrix.mul_smul, Matrix.smul_mul]
  rw [hsplit, hcomm.mul_pow] at hk
  have hz2 : z ^ (2 ^ k) ∈ (rho (K := F)).range := by
    have e1 : z ^ (2 ^ k) = (rho (P', Q') ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_right hk
    rw [e1]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩) _)
  have he1 := eq_one_of_pow_two_pow h4 (eq_one_of_actsSmul_mem_range (hzs.pow _) hz2)
  have hz1 : z = 1 := (show ActsSmul z 1 from he1 ▸ hzs).eq_one
  rw [hsplit, hz1, mul_one]
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

theorem isNS_trM_conj {x : MulAut (VM F)} (hx : IsNS x) : IsNS (trM * x * trM⁻¹) := by
  obtain ⟨A, B, τ, rfl⟩ := hx
  have htinv : (trM : MulAut (VM F))⁻¹ = trM := inv_eq_of_mul_eq_one_right trM_mul_self
  refine ⟨B, A, τ, ?_⟩
  rw [htinv, ← mul_assoc, trM_lr, mul_assoc (lr B A), trM_frM, ← mul_assoc, mul_assoc,
    trM_mul_self, mul_one]

theorem isNS_conj [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) {n x : MulAut (VM F)}
    (hn : n ∈ Subgroup.normalizer ((rho (K := F)).range : Set (MulAut (VM F)))) (hx : IsNS x) :
    IsNS (n * x * n⁻¹) := by
  obtain ⟨A, B, τ, h | h⟩ := exists_eq_of_mem_normalizer h4 hn
  · have hm : IsNS n := ⟨A, B, τ, h⟩
    exact (hm.mul hx).mul hm.inv
  · have hm : IsNS (lr A B * frM τ) := ⟨A, B, τ, rfl⟩
    rw [h]
    have e : lr A B * frM τ * trM * x * (lr A B * frM τ * trM)⁻¹ =
        (lr A B * frM τ) * (trM * x * trM⁻¹) * (lr A B * frM τ)⁻¹ := by group
    rw [e]
    exact (hm.mul (isNS_trM_conj hx)).mul hm.inv

theorem not_isNS_tA (A : GL (Fin 2) F) : ¬ IsNS (lr A A⁻¹ * trM) := by
  intro h
  apply not_isNS_trM (K := F)
  have e : (trM : MulAut (VM F)) = (lr A A⁻¹)⁻¹ * (lr A A⁻¹ * trM) := by group
  rw [e]
  exact (show IsNS (lr A A⁻¹)⁻¹ from (show IsNS (lr A A⁻¹) from
    ⟨A, A⁻¹, 1, by rw [frM_one, mul_one]⟩).inv).mul h

theorem isNS_swap_mul (A P Q : GL (Fin 2) F) (τ : F ≃+* F) :
    IsNS ((lr P Q * frM τ * trM) * (lr A A⁻¹ * trM)) := by
  have e : (lr P Q * frM τ * trM) * (lr A A⁻¹ * trM) = (lr P Q * frM τ) * lr A⁻¹ A := by
    calc (lr P Q * frM τ * trM) * (lr A A⁻¹ * trM)
        = lr P Q * frM τ * (trM * lr A A⁻¹) * trM := by group
      _ = lr P Q * frM τ * (lr A⁻¹ A * trM) * trM := by rw [trM_lr]
      _ = lr P Q * frM τ * lr A⁻¹ A * (trM * trM) := by group
      _ = _ := by rw [trM_mul_self, mul_one]
  rw [e]
  exact (show IsNS (lr P Q * frM τ) from ⟨P, Q, τ, rfl⟩).mul
    ⟨A⁻¹, A, 1, by rw [frM_one, mul_one]⟩

theorem diag_eq_of_comm [CharP F 2] {g h : SpecialLinearGroup (Fin 2) F} {A : GL (Fin 2) F}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (hh : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hA : IsUT A)
    (hc : rho (g, h) * (lr A A⁻¹ * trM) * (rho (g, h))⁻¹ * (lr A A⁻¹ * trM)⁻¹ ∈ sZero) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 = (h : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set G := Matrix.SpecialLinearGroup.toGL g with hG
  set H := Matrix.SpecialLinearGroup.toGL h with hH
  have htinv : (lr A A⁻¹ * trM)⁻¹ = lr A A⁻¹ * trM :=
    inv_eq_of_mul_eq_one_right (by
      rw [mul_assoc, ← mul_assoc trM, trM_lr, mul_assoc, trM_mul_self, mul_one, lr_mul,
        mul_inv_cancel, inv_mul_cancel, lr_one])
  have e : rho (g, h) * (lr A A⁻¹ * trM) * (rho (g, h))⁻¹ * (lr A A⁻¹ * trM)⁻¹ =
      lr (G * A * H⁻¹ * A⁻¹) (H * A⁻¹ * G⁻¹ * A) := by
    rw [htinv, ← map_inv, rho_apply, rho_apply, Prod.inv_mk, map_inv, map_inv]
    calc lr G H * (lr A A⁻¹ * trM) * lr G⁻¹ H⁻¹ * (lr A A⁻¹ * trM)
        = lr G H * lr A A⁻¹ * (trM * lr G⁻¹ H⁻¹) * lr A A⁻¹ * trM := by group
      _ = lr G H * lr A A⁻¹ * lr H⁻¹ G⁻¹ * (trM * lr A A⁻¹) * trM := by rw [trM_lr]; group
      _ = lr G H * lr A A⁻¹ * lr H⁻¹ G⁻¹ * lr A⁻¹ A * (trM * trM) := by rw [trM_lr]; group
      _ = _ := by rw [trM_mul_self, mul_one, lr_mul, lr_mul, lr_mul]
  rw [e] at hc
  obtain ⟨p, q, hpq⟩ := hc
  rw [rho_apply] at hpq
  have e3 : lr ((Matrix.SpecialLinearGroup.toGL (utS p))⁻¹ * (G * A * H⁻¹ * A⁻¹))
      ((Matrix.SpecialLinearGroup.toGL (utS q))⁻¹ * (H * A⁻¹ * G⁻¹ * A)) = 1 := by
    rw [← lr_mul, hpq, lr_mul, inv_mul_cancel, inv_mul_cancel, lr_one]
  obtain ⟨c, hc, -⟩ := exists_smul_of_lr_eq_one e3
  have hX : ((G * A * H⁻¹ * A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      c • ((utS p : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun M => ((utS p : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) * M) hc
    simp only [Units.val_mul] at this
    rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_GL_coe_matrix (utS p),
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one] at this
    simpa only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using this
  have h00 := congrFun (congrFun hX 0) 0
  have h11 := congrFun (congrFun hX 1) 1
  obtain ⟨hA10, hA00, hA11⟩ := ut_inv_entries hA
  have hAu : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hA
  have hGu : (G : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hg
  have hHU : IsUT H := hh
  obtain ⟨hH10, hH00, hH11⟩ := ut_inv_entries hHU
  have hGH : (G : Matrix (Fin 2) (Fin 2) F) 0 0 * (G : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 :=
    sl_ut_det hg
  have hHH : (H : Matrix (Fin 2) (Fin 2) F) 0 0 * (H : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 :=
    sl_ut_det hh
  simp only [Units.val_mul] at h00 h11
  obtain ⟨o1, o2, o3⟩ := ut_mul_entries hGu hAu
  obtain ⟨n1, n2, n3⟩ := ut_mul_entries o1 hH10
  obtain ⟨-, m2, m3⟩ := ut_mul_entries n1 hA10
  have r00 : (c • ((utS p : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) 0 0 = c := by
    simp [coe_utS]
  have r11 : (c • ((utS p : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) 1 1 = c := by
    simp [coe_utS]
  rw [m2, n2, o2, r00] at h00
  rw [m3, n3, o3, r11] at h11
  set a := (G : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set a' := (G : Matrix (Fin 2) (Fin 2) F) 1 1 with ha'
  set b := (H : Matrix (Fin 2) (Fin 2) F) 0 0 with hb
  set b' := (H : Matrix (Fin 2) (Fin 2) F) 1 1 with hb'
  set u := ((H⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 with hu
  set v := ((H⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 with hv
  set x := (A : Matrix (Fin 2) (Fin 2) F) 0 0 with hx
  set x' := ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 with hx'
  set y := (A : Matrix (Fin 2) (Fin 2) F) 1 1 with hy
  set y' := ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 with hy'
  have E1 : a * u = c := by linear_combination h00 - a * u * hA00
  have E2 : a' * v = c := by linear_combination h11 - a' * v * hA11
  have key : a * a - b * b = 0 := by
    linear_combination (a * b) * (E1 - E2) - a ^ 2 * hH00 + b * v * hGH - b * v * hHH +
      b ^ 2 * hH11
  have h3 : (a + b) * (a + b) = 0 := by linear_combination key + (a * b + b * b) * h2
  have h4 := mul_self_eq_zero.mp h3
  change a = b
  linear_combination h4 - b * h2

end CFSG.Quasithin.H13.L32A.L2
