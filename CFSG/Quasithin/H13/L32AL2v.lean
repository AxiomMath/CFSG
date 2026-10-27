module

public import CFSG.Quasithin.H13.L32AL2u

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Quasithin.H.Om4 Matrix

variable {F : Type} [Field F]

@[expose] def conjSL (A : GL (Fin 2) F) (g : SpecialLinearGroup (Fin 2) F) :
    SpecialLinearGroup (Fin 2) F :=
  ⟨((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) *
    (A : Matrix (Fin 2) (Fin 2) F), by
    rw [Matrix.det_mul, Matrix.det_mul, g.2, mul_one, ← Matrix.det_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.det_one]⟩

theorem coe_conjSL (A : GL (Fin 2) F) (g : SpecialLinearGroup (Fin 2) F) :
    ((conjSL A g : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) *
        (A : Matrix (Fin 2) (Fin 2) F) := rfl

theorem conjSL_conjSL_inv (A : GL (Fin 2) F) (g : SpecialLinearGroup (Fin 2) F) :
    conjSL A (conjSL A⁻¹ g) = g := by
  ext i j
  rw [coe_conjSL, coe_conjSL, inv_inv]
  have h1 : ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (A : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mul_assoc, h1, Matrix.mul_one]

theorem conj_rho_conjSL (A : GL (Fin 2) F) (g : SpecialLinearGroup (Fin 2) F) :
    (lr A 1)⁻¹ * rho (g, conjSL A g) * lr A 1 = rho (conjSL A g, conjSL A g) := by
  rw [rho_apply, rho_apply, lr_inv, lr_mul, lr_mul, inv_one, one_mul, mul_one]
  congr 1
  exact Units.ext (by rw [Units.val_mul, Units.val_mul]; rfl)

theorem conj_diag_eq (A B : GL (Fin 2) F) (τ : F ≃+* F) (G : GL (Fin 2) F) :
    (lr A B * frM τ) * lr G G * (lr A B * frM τ)⁻¹ =
      lr (A * GeneralLinearGroup.map τ.toRingHom G * A⁻¹)
        (B * GeneralLinearGroup.map τ.toRingHom G * B⁻¹) := by
  rw [mul_inv_eq_iff_eq_mul, mul_assoc, frM_lr, ← mul_assoc, lr_mul, ← mul_assoc, lr_mul,
    inv_mul_cancel_right, inv_mul_cancel_right]

@[expose] def ltS (p : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; p, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_ltS (p : F) : ((ltS p : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![1, 0; p, 1] := rfl

theorem eq_smul_one_of_comm {M : Matrix (Fin 2) (Fin 2) F}
    (hu : M * !![1, 1; 0, 1] = !![1, 1; 0, 1] * M) (hl : M * !![1, 0; 1, 1] = !![1, 0; 1, 1] * M) :
    M = M 0 0 • 1 := by
  have u10 : M 1 0 = 0 := by
    have := congrFun (congrFun hu 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    exact this
  have u11 : M 1 1 = M 0 0 := by
    have := congrFun (congrFun hu 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination -this
  have l01 : M 0 1 = 0 := by
    have := congrFun (congrFun hl 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    exact this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u10, u11, l01]

theorem coe_map_utS (τ : F ≃+* F) (x : F) :
    ((GeneralLinearGroup.map τ.toRingHom (Matrix.SpecialLinearGroup.toGL (utS x)) :
      GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, τ x; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.map_apply, coe_utS]

theorem coe_map_ltS (τ : F ≃+* F) (x : F) :
    ((GeneralLinearGroup.map τ.toRingHom (Matrix.SpecialLinearGroup.toGL (ltS x)) :
      GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; τ x, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.map_apply, coe_ltS]

theorem comm_of_lr_eq [CharP F 2] {C D G : GL (Fin 2) F} {τ : F ≃+* F}
    (hG : (G : Matrix (Fin 2) (Fin 2) F).det = 1)
    (h : lr (C * GeneralLinearGroup.map τ.toRingHom G * C⁻¹)
      (D * GeneralLinearGroup.map τ.toRingHom G * D⁻¹) = lr G G) :
    C * GeneralLinearGroup.map τ.toRingHom G = G * C ∧
      D * GeneralLinearGroup.map τ.toRingHom G = G * D := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set X := C * GeneralLinearGroup.map τ.toRingHom G * C⁻¹ with hX
  set Y := D * GeneralLinearGroup.map τ.toRingHom G * D⁻¹ with hY
  have e : lr (G⁻¹ * X) (G⁻¹ * Y) = 1 := by
    rw [← lr_mul, h, lr_mul, inv_mul_cancel, lr_one]
  obtain ⟨c, hc, hc1⟩ := exists_smul_of_lr_eq_one e
  have hG' : Matrix.GeneralLinearGroup.det G = 1 := Units.ext hG
  have hτG : Matrix.GeneralLinearGroup.det (GeneralLinearGroup.map τ.toRingHom G) = 1 := by
    rw [Matrix.GeneralLinearGroup.map_det, hG', map_one]
  have hdU : Matrix.GeneralLinearGroup.det (G⁻¹ * X) = 1 := by
    rw [hX]
    simp only [map_mul, map_inv, hG', hτG, inv_one, mul_one, mul_inv_cancel]
  have hdet : ((G⁻¹ * X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    have := congrArg Units.val hdU
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
  rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hc1' : c = 1 := by
    have h3 : (c + 1) * (c + 1) = 0 := by linear_combination hdet + (c + 1) * h2
    linear_combination mul_self_eq_zero.mp h3 - h2
  rw [hc1', one_smul] at hc
  have eX : G⁻¹ * X = 1 := Units.ext hc
  rw [hc, Matrix.one_mul] at hc1
  have eY : G⁻¹ * Y = 1 := by
    apply Units.ext
    have := congrArg Matrix.transpose hc1
    rwa [Matrix.transpose_transpose, Matrix.transpose_one] at this
  constructor
  · calc C * GeneralLinearGroup.map τ.toRingHom G = G * (G⁻¹ * X) * C := by rw [hX]; group
      _ = G * C := by rw [eX, mul_one]
  · calc D * GeneralLinearGroup.map τ.toRingHom G = G * (G⁻¹ * Y) * D := by rw [hY]; group
      _ = G * D := by rw [eY, mul_one]

theorem scalar_of_comm_diag [CharP F 2] {A B : GL (Fin 2) F} {τ : F ≃+* F}
    (h : ∀ G : GL (Fin 2) F, (G : Matrix (Fin 2) (Fin 2) F).det = 1 →
      lr (A * GeneralLinearGroup.map τ.toRingHom G * A⁻¹)
        (B * GeneralLinearGroup.map τ.toRingHom G * B⁻¹) = lr G G) :
    τ = 1 ∧ (∃ a : F, (A : Matrix (Fin 2) (Fin 2) F) = a • 1) ∧
      ∃ b : F, (B : Matrix (Fin 2) (Fin 2) F) = b • 1 := by
  have key : ∀ x : F, ∀ (C D : GL (Fin 2) F), (∀ G : GL (Fin 2) F,
      (G : Matrix (Fin 2) (Fin 2) F).det = 1 → lr (C * GeneralLinearGroup.map τ.toRingHom G * C⁻¹)
        (D * GeneralLinearGroup.map τ.toRingHom G * D⁻¹) = lr G G) →
      (C : Matrix (Fin 2) (Fin 2) F) * !![1, τ x; 0, 1] = !![1, x; 0, 1] * C ∧
        (C : Matrix (Fin 2) (Fin 2) F) * !![1, 0; τ x, 1] = !![1, 0; x, 1] * C := by
    intro x C D hCD
    have hu := (comm_of_lr_eq (G := Matrix.SpecialLinearGroup.toGL (utS x)) (utS x).2
      (hCD (Matrix.SpecialLinearGroup.toGL (utS x)) (utS x).2)).1
    have hl := (comm_of_lr_eq (G := Matrix.SpecialLinearGroup.toGL (ltS x)) (ltS x).2
      (hCD (Matrix.SpecialLinearGroup.toGL (ltS x)) (ltS x).2)).1
    have eu := congrArg Units.val hu
    have el := congrArg Units.val hl
    rw [Units.val_mul, Units.val_mul, coe_map_utS, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      coe_utS] at eu
    rw [Units.val_mul, Units.val_mul, coe_map_ltS, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      coe_ltS] at el
    exact ⟨eu, el⟩
  have hsw : ∀ X Y : GL (Fin 2) F, lr Y X = trM * lr X Y * trM := fun X Y => by
    rw [trM_lr, mul_assoc, trM_mul_self, mul_one]
  have h' : ∀ G : GL (Fin 2) F, (G : Matrix (Fin 2) (Fin 2) F).det = 1 →
      lr (B * GeneralLinearGroup.map τ.toRingHom G * B⁻¹)
        (A * GeneralLinearGroup.map τ.toRingHom G * A⁻¹) = lr G G := by
    intro G hG
    rw [hsw, h G hG, ← hsw]
  obtain ⟨hAu, hAl⟩ := key 1 A B h
  obtain ⟨hBu, hBl⟩ := key 1 B A h'
  rw [map_one] at hAu hAl hBu hBl
  have hAs := eq_smul_one_of_comm hAu hAl
  have hBs := eq_smul_one_of_comm hBu hBl
  have hA0 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h0
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit
    rw [hAs, h0, zero_smul, Matrix.det_zero] at hd
    exact not_isUnit_zero hd
  refine ⟨RingEquiv.ext fun x => ?_, ⟨_, hAs⟩, ⟨_, hBs⟩⟩
  have e := congrFun (congrFun (key x A B h).1 0) 1
  rw [hAs] at e
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e
  exact mul_left_cancel₀ hA0 (e.trans (mul_comm x _))

@[expose] def ActsSmul (z : MulAut (VM F)) (e : F) : Prop :=
  ∀ X : Matrix (Fin 2) (Fin 2) F, Multiplicative.toAdd (z (Multiplicative.ofAdd X)) = e • X

theorem ActsSmul.pow {z : MulAut (VM F)} {e : F} (h : ActsSmul z e) (n : ℕ) :
    ActsSmul (z ^ n) (e ^ n) := by
  induction n with
  | zero =>
    intro X
    rw [pow_zero, pow_zero, MulAut.one_apply, toAdd_ofAdd, one_smul]
  | succ n ih =>
    intro X
    rw [pow_succ, pow_succ, MulAut.mul_apply, ← ofAdd_toAdd (z (Multiplicative.ofAdd X)), h X, ih,
      smul_smul]

theorem ActsSmul.eq_one {z : MulAut (VM F)} (h : ActsSmul z 1) : z = 1 := by
  refine MulEquiv.ext fun X => ?_
  apply Multiplicative.toAdd.injective
  rw [MulAut.one_apply]
  have := h (Multiplicative.toAdd X)
  rwa [ofAdd_toAdd, one_smul] at this

theorem ActsSmul.pow_eq_one {z : MulAut (VM F)} {e : F} (h : ActsSmul z e) {n : ℕ}
    (hn : z ^ n = 1) : e ^ n = 1 := by
  have h1 := (h.pow n) 1
  rw [hn, MulAut.one_apply, toAdd_ofAdd] at h1
  have := congrFun (congrFun h1 0) 0
  simpa using this.symm

theorem eq_one_of_pow_two_pow [Finite F] (h4 : Nat.card F = 4) {e : F} {k : ℕ}
    (he : e ^ (2 ^ k) = 1) : e = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, h4]
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at he
    exact zero_ne_one he
  have h3 : e ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one e he0
    rwa [hcard] at this
  have hd : orderOf e ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one he) (orderOf_dvd_of_pow_eq_one h3)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (by norm_num)), Nat.dvd_one,
    orderOf_eq_one_iff] at hd
  exact hd

theorem eq_of_comm_diag [Finite F] [CharP F 2] (h4 : Nat.card F = 4) (A : GL (Fin 2) F)
    {y : MulAut (VM F)}
    (hy : y ∈ Subgroup.normalizer ((rho (K := F)).range : Set (MulAut (VM F))))
    {k : ℕ} (hk : y ^ (2 ^ k) = 1)
    (hc : ∀ g : SpecialLinearGroup (Fin 2) F, y * rho (g, conjSL A g) = rho (g, conjSL A g) * y) :
    y = 1 ∨ y = lr A A⁻¹ * trM := by
  obtain ⟨y', hy'⟩ : ∃ y' : MulAut (VM F), y' = (lr A 1)⁻¹ * y * lr A 1 := ⟨_, rfl⟩
  have hyy : y = lr A 1 * y' * (lr A 1)⁻¹ := by rw [hy']; group
  have hy'N : y' ∈ Subgroup.normalizer ((rho (K := F)).range : Set (MulAut (VM F))) := by
    rw [hy']
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (lr_mem_normalizer A 1)) hy)
      (lr_mem_normalizer A 1)
  have hU : ∀ G : GL (Fin 2) F, (G : Matrix (Fin 2) (Fin 2) F).det = 1 →
      y' * lr G G * y'⁻¹ = lr G G := by
    intro G hG
    set g : SpecialLinearGroup (Fin 2) F := ⟨_, hG⟩ with hg
    have hGg : Matrix.SpecialLinearGroup.toGL g = G := Units.ext rfl
    have e1 := conj_rho_conjSL A (conjSL A⁻¹ g)
    rw [conjSL_conjSL_inv, rho_apply, rho_apply, hGg] at e1
    have e2 := hc (conjSL A⁻¹ g)
    rw [conjSL_conjSL_inv, rho_apply, hGg] at e2
    generalize lr (Matrix.SpecialLinearGroup.toGL (conjSL A⁻¹ g)) G = R at e1 e2
    generalize lr A 1 = L at e1 hy'
    rw [hy', ← e1]
    calc L⁻¹ * y * L * (L⁻¹ * R * L) * (L⁻¹ * y * L)⁻¹ = L⁻¹ * (y * R) * y⁻¹ * L := by group
      _ = L⁻¹ * R * L := by rw [e2]; group
  obtain ⟨P, Q, τ, hform⟩ := exists_eq_of_mem_normalizer (by omega) hy'N
  have hconj : ∀ G : GL (Fin 2) F, y' * lr G G * y'⁻¹ =
      lr (P * GeneralLinearGroup.map τ.toRingHom G * P⁻¹)
        (Q * GeneralLinearGroup.map τ.toRingHom G * Q⁻¹) := by
    intro G
    rcases hform with h | h
    · rw [h, conj_diag_eq]
    · rw [h]
      exact S153G93D.Om4P.conj_swap P Q G G τ
  obtain ⟨hτ, ⟨a, ha⟩, ⟨b, hb⟩⟩ := scalar_of_comm_diag (A := P) (B := Q) (τ := τ) fun G hG => by
    rw [← hconj G, hU G hG]
  subst hτ
  have hlr : ∀ X : Matrix (Fin 2) (Fin 2) F,
      Multiplicative.toAdd (lr P Q (Multiplicative.ofAdd X)) = (a * b) • X := by
    intro X
    rw [toAdd_lr, toAdd_ofAdd, ha, hb, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm b a]
  have hk' : y' ^ (2 ^ k) = 1 := by
    rw [hy', show (lr A 1)⁻¹ * y * lr A 1 = (MulAut.conj (lr A 1)⁻¹) y by
      rw [MulAut.conj_apply, inv_inv], ← map_pow, hk, map_one]
  rcases hform with h | h
  ·
    rw [frM_one, mul_one] at h
    have hs : ActsSmul y' (a * b) := fun X => by rw [h, hlr]
    have he := eq_one_of_pow_two_pow h4 (hs.pow_eq_one hk')
    left
    rw [hyy, (he ▸ hs : ActsSmul y' 1).eq_one, mul_one, mul_inv_cancel]
  · rw [frM_one, mul_one] at h
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · left
      rwa [pow_zero, pow_one] at hk
    have hs1 : ∀ X : Matrix (Fin 2) (Fin 2) F,
        Multiplicative.toAdd (y' (Multiplicative.ofAdd X)) = (a * b) • Xᵀ := fun X => by
      rw [h, MulAut.mul_apply, ← ofAdd_toAdd (trM (Multiplicative.ofAdd X)), hlr, toAdd_trM,
        toAdd_ofAdd]
    have hs2 : ActsSmul (y' ^ 2) ((a * b) ^ 2) := fun X => by
      rw [show y' ^ 2 = y' * y' from pow_two y', MulAut.mul_apply,
        ← ofAdd_toAdd (y' (Multiplicative.ofAdd X)), hs1, hs1, Matrix.transpose_smul,
        Matrix.transpose_transpose, smul_smul, pow_two]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk2 : (y' ^ 2) ^ (2 ^ k') = 1 := by rwa [← pow_mul, ← pow_succ']
    have he := eq_one_of_pow_two_pow h4 (k := k' + 1)
      (by rw [pow_succ', pow_mul]; exact hs2.pow_eq_one hk2)
    have hy'1 : y' = trM := by
      rw [h]
      have hl : lr P Q = 1 := (show ActsSmul (lr P Q) 1 from fun X => by rw [hlr, he]).eq_one
      rw [hl, one_mul]
    right
    rw [hyy, hy'1, lr_inv, inv_one, mul_assoc, trM_lr, ← mul_assoc, lr_mul, mul_one, one_mul]

end CFSG.Quasithin.H13.L32A.L2
