module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5TorusB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H.Om4 Matrix

variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def s16c11_case5_lrHom :
    GL (Fin 2) K × GL (Fin 2) K →* MulAut (VM K) where
  toFun p := lr p.1 p.2
  map_one' := by rw [Prod.fst_one, Prod.snd_one, lr_one]
  map_mul' p q := by rw [Prod.fst_mul, Prod.snd_mul, lr_mul]

@[expose] noncomputable def s16c11_case5_lrRange : Subgroup (MulAut (VM K)) :=
  s16c11_case5_lrHom.range

@[expose] noncomputable def s16c11_case5_Omega : Subgroup (MulAut (VM K)) := (rho (K := K)).range

@[expose] noncomputable def s16c11_case5_N1 : Subgroup (MulAut (VM K)) :=
  Subgroup.normalizer (s16c11_case5_Omega (K := K) : Set (MulAut (VM K))) ⊓
    Subgroup.centralizer (s16c11C5Scal K : Set (MulAut (VM K)))

@[expose] noncomputable def s16c11_case5_S0 : Subgroup (MulAut (VM K)) :=
  s16c11_case5_V ⊔ Subgroup.zpowers (s16c11_case5_sigma (K := K))

theorem s16c11_case5_mem_lrRange {x : MulAut (VM K)} :
    x ∈ s16c11_case5_lrRange ↔ ∃ A B : GL (Fin 2) K, x = lr A B := by
  rw [s16c11_case5_lrRange, MonoidHom.mem_range]
  constructor
  · rintro ⟨⟨A, B⟩, h⟩
    exact ⟨A, B, by simpa [s16c11_case5_lrHom] using h.symm⟩
  · rintro ⟨A, B, h⟩
    exact ⟨(A, B), by simpa [s16c11_case5_lrHom] using h.symm⟩

theorem s16c11_case5_lr_inj_left (A A' B : GL (Fin 2) K) (h : lr A B = lr A' B) : A = A' := by
  have key : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (A : Matrix (Fin 2) (Fin 2) K) * X * (B : Matrix (Fin 2) (Fin 2) K)ᵀ =
        (A' : Matrix (Fin 2) (Fin 2) K) * X * (B : Matrix (Fin 2) (Fin 2) K)ᵀ := by
    intro X
    have := congrArg (fun f : MulAut (VM K) =>
      Multiplicative.toAdd (f (Multiplicative.ofAdd X))) h
    simpa [toAdd_lr] using this
  have hB : ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ *
      (B : Matrix (Fin 2) (Fin 2) K)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one]
  have h1 := key (((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ)
  simp only [Matrix.mul_assoc, hB, Matrix.mul_one] at h1
  exact Units.ext h1

section Normalizer

variable [CharP K 2]

theorem s16c11_case5_scalar_comm (u : Kˣ) (A : GL (Fin 2) K) :
    A * Matrix.GeneralLinearGroup.scalar (Fin 2) u =
      Matrix.GeneralLinearGroup.scalar (Fin 2) u * A := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply] <;> ring

theorem s16c11_case5_matrix_scalar_comm (u : Kˣ) (X : Matrix (Fin 2) (Fin 2) K) :
    X * (Matrix.GeneralLinearGroup.scalar (Fin 2) u : Matrix (Fin 2) (Fin 2) K) =
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u : Matrix (Fin 2) (Fin 2) K) * X := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem s16c11_case5_lr_scalar_swap (u : Kˣ) :
    lr 1 (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      lr (Matrix.GeneralLinearGroup.scalar (Fin 2) u) 1 := by
  refine MulEquiv.ext fun X => ?_
  apply Multiplicative.toAdd.injective
  rw [toAdd_lr, toAdd_lr, Units.val_one, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
  rw [show ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : Matrix (Fin 2) (Fin 2) K))ᵀ =
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u : Matrix (Fin 2) (Fin 2) K) by
    ext i j
    simp [Matrix.transpose_apply, Matrix.diagonal_apply, eq_comm]]
  exact s16c11_case5_matrix_scalar_comm u X

theorem s16c11_case5_scalar_conj_trM (u : Kˣ) :
    (trM : MulAut (VM K)) * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) u) 1 * trM⁻¹ =
      lr (Matrix.GeneralLinearGroup.scalar (Fin 2) u) 1 := by
  rw [trM_lr, s16c11_case5_lr_scalar_swap, mul_assoc, mul_inv_cancel, mul_one]

theorem s16c11_case5_lr_scalar_comm (A B : GL (Fin 2) K) (u : Kˣ) :
    lr A B * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) u) 1 =
      lr (Matrix.GeneralLinearGroup.scalar (Fin 2) u) 1 * lr A B := by
  rw [lr_mul, lr_mul, mul_one, one_mul, s16c11_case5_scalar_comm]

theorem s16c11_case5_conj_scalar_frM (A B : GL (Fin 2) K) (τ : K ≃+* K) (c : Kˣ) :
    (lr A B * frM τ) * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 *
        (lr A B * frM τ)⁻¹ =
      lr (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map τ.toRingHom c)) 1 := by
  have hfr : frM τ * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 * (frM τ)⁻¹ =
      lr (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map τ.toRingHom c)) 1 := by
    rw [frM_lr, map_one, GeneralLinearGroup.map_scalar]
    group
  have hcomm := s16c11_case5_lr_scalar_comm A B (Units.map τ.toRingHom c)
  calc (lr A B * frM τ) * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 *
        (lr A B * frM τ)⁻¹
      = lr A B * (frM τ * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 * (frM τ)⁻¹) *
        (lr A B)⁻¹ := by group
    _ = lr A B * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map τ.toRingHom c)) 1 *
        (lr A B)⁻¹ := by rw [hfr]
    _ = lr (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map τ.toRingHom c)) 1 := by
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem s16c11_case5_conj_scalar_frM_trM (A B : GL (Fin 2) K) (τ : K ≃+* K) (c : Kˣ) :
    (lr A B * frM τ * trM) * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 *
        (lr A B * frM τ * trM)⁻¹ =
      lr (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map τ.toRingHom c)) 1 := by
  have ht := s16c11_case5_scalar_conj_trM c
  have hfr : frM τ * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 * (frM τ)⁻¹ =
      lr (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map τ.toRingHom c)) 1 := by
    rw [frM_lr, map_one, GeneralLinearGroup.map_scalar]
    group
  have hcomm := s16c11_case5_lr_scalar_comm A B (Units.map τ.toRingHom c)
  calc (lr A B * frM τ * trM) * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 *
        (lr A B * frM τ * trM)⁻¹
      = lr A B * frM τ * (trM * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 * trM⁻¹) *
        (frM τ)⁻¹ * (lr A B)⁻¹ := by group
    _ = lr A B * frM τ * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 * (frM τ)⁻¹ *
        (lr A B)⁻¹ := by rw [ht]
    _ = lr A B * (frM τ * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 * (frM τ)⁻¹) *
        (lr A B)⁻¹ := by group
    _ = lr A B * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map τ.toRingHom c)) 1 *
        (lr A B)⁻¹ := by rw [hfr]
    _ = lr (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map τ.toRingHom c)) 1 := by
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem s16c11_case5_frM_eq_one {x : MulAut (VM K)}
    (hx : x ∈ Subgroup.centralizer (s16c11C5Scal K : Set (MulAut (VM K))))
    {A B : GL (Fin 2) K} {τ : K ≃+* K}
    (h : x = lr A B * frM τ ∨ x = lr A B * frM τ * trM) : τ = 1 := by
  have key : ∀ c : Kˣ,
      lr (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map τ.toRingHom c)) 1 =
      lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 := by
    intro c
    have hmem : lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 ∈ s16c11C5Scal K :=
      Subgroup.subset_closure ⟨c, rfl⟩
    have hc := (Subgroup.mem_centralizer_iff.mp hx) _ hmem
    have hconj : x * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 * x⁻¹ =
        lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 := by
      rw [hc.symm, mul_assoc, mul_inv_cancel, mul_one]
    rcases h with h | h
    · rw [h, s16c11_case5_conj_scalar_frM] at hconj
      exact hconj
    · rw [h, s16c11_case5_conj_scalar_frM_trM] at hconj
      exact hconj
  have hτc : ∀ c : Kˣ, (τ c : K) = c := by
    intro c
    have h2 : Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map τ.toRingHom c) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) c :=
      s16c11_case5_lr_inj_left _ _ 1 (key c)
    have h3 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h2
    simpa [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply] using h3
  ext x
  by_cases hx0 : x = 0
  · subst hx0
    exact map_zero τ
  · have := hτc (Units.mk0 x hx0)
    simpa using this

theorem s16c11_case5_frM_one : frM (1 : K ≃+* K) = 1 := by
  ext X
  apply Multiplicative.ofAdd.injective
  simp [frM]

omit [CharP K 2] in
theorem s16c11_case5_t_inv (μ : Kˣ) :
    (s16c11_case5_t μ)⁻¹ = s16c11_case5_t μ⁻¹ := by
  apply Subtype.ext
  simp only [s16c11_case5_t, SpecialLinearGroup.diag2_inv, SpecialLinearGroup.diag2_coe',
    Units.val_inv_eq_inv_val]

omit [CharP K 2] in
theorem s16c11_case5_t_conj_u (μ : Kˣ) (a : K) :
    s16c11_case5_t μ * s16c11_case5_u a * (s16c11_case5_t μ)⁻¹ =
      s16c11_case5_u ((μ : K) ^ 2 * a) := by
  rw [s16c11_case5_t_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp only [s16c11_case5_t, s16c11_case5_u, tv, SpecialLinearGroup.diag2_coe,
    Matrix.transvection]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
      Matrix.one_mul, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply,
      Matrix.single_apply, Matrix.add_apply, pow_two, Units.val_inv_eq_inv_val] <;>
    field_simp [μ.ne_zero] <;> ring

omit [CharP K 2] in
theorem s16c11_case5_D0_conj_rhoU (μ : Kˣ) (a b : K) :
    s16c11_case5_D0Hom μ * s16c11_case5_rhoU a b * (s16c11_case5_D0Hom μ)⁻¹ =
      s16c11_case5_rhoU ((μ : K) ^ 2 * a) ((μ : K) ^ 2 * b) := by
  change rho (s16c11_case5_t μ, s16c11_case5_t μ) * s16c11_case5_rhoU a b *
      (rho (s16c11_case5_t μ, s16c11_case5_t μ))⁻¹ =
      s16c11_case5_rhoU ((μ : K) ^ 2 * a) ((μ : K) ^ 2 * b)
  rw [s16c11_case5_rhoU, s16c11_case5_rhoU, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  exact Prod.ext (s16c11_case5_t_conj_u μ a) (s16c11_case5_t_conj_u μ b)

omit [CharP K 2] in
theorem s16c11_case5_D0_comm_sigma (μ : Kˣ) :
    s16c11_case5_D0Hom μ * s16c11_case5_sigma =
      s16c11_case5_sigma * s16c11_case5_D0Hom μ := by
  change lr (Matrix.SpecialLinearGroup.toGL (s16c11_case5_t μ))
      (Matrix.SpecialLinearGroup.toGL (s16c11_case5_t μ)) * trM =
    trM * lr (Matrix.SpecialLinearGroup.toGL (s16c11_case5_t μ))
      (Matrix.SpecialLinearGroup.toGL (s16c11_case5_t μ))
  rw [trM_lr]

theorem s16c11_case5_lr_mem_centralizer_scal (A B : GL (Fin 2) K) :
    lr A B ∈ Subgroup.centralizer (s16c11C5Scal K : Set (MulAut (VM K))) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  induction hz using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨c, rfl⟩ := hy
      exact (s16c11_case5_lr_scalar_comm A B c).symm
  | one => rw [one_mul, mul_one]
  | mul y z hy hz ihy ihz => rw [mul_assoc, ihz, ← mul_assoc, ihy, mul_assoc]
  | inv y hy ihy =>
      have h : y⁻¹ * lr A B = lr A B * y⁻¹ := by
        calc y⁻¹ * lr A B = y⁻¹ * (lr A B * y) * y⁻¹ := by group
          _ = y⁻¹ * (y * lr A B) * y⁻¹ := by rw [← ihy]
          _ = lr A B * y⁻¹ := by group
      exact h

theorem s16c11_case5_trM_mem_centralizer_scal :
    (trM : MulAut (VM K)) ∈
      Subgroup.centralizer (s16c11C5Scal K : Set (MulAut (VM K))) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  induction hz using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨c, rfl⟩ := hy
      have h : (trM : MulAut (VM K)) * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 =
          lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 * trM := by
        calc (trM : MulAut (VM K)) * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1
            = (trM * lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 * trM⁻¹) * trM := by group
          _ = lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) 1 * trM := by
              rw [s16c11_case5_scalar_conj_trM]
      exact h.symm
  | one => rw [one_mul, mul_one]
  | mul y z hy hz ihy ihz => rw [mul_assoc, ihz, ← mul_assoc, ihy, mul_assoc]
  | inv y hy ihy =>
      have h : y⁻¹ * (trM : MulAut (VM K)) = trM * y⁻¹ := by
        calc y⁻¹ * (trM : MulAut (VM K)) = y⁻¹ * (trM * y) * y⁻¹ := by group
          _ = y⁻¹ * (y * trM) * y⁻¹ := by rw [← ihy]
          _ = trM * y⁻¹ := by group
      exact h

theorem s16c11_case5_trM_conj_lr (A B : GL (Fin 2) K) :
    (trM : MulAut (VM K)) * lr A B * trM = lr B A := by
  rw [trM_lr, mul_assoc, trM_mul_self, mul_one]

theorem s16c11_case5_trM_mem_normalizer :
    (trM : MulAut (VM K)) ∈
      Subgroup.normalizer (s16c11_case5_Omega (K := K) : Set (MulAut (VM K))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [s16c11_case5_Omega, MonoidHom.mem_range] at hy ⊢
    obtain ⟨⟨g, h⟩, rfl⟩ := hy
    refine ⟨(h, g), ?_⟩
    rw [rho_apply, rho_apply]
    rw [show (trM : MulAut (VM K))⁻¹ = trM from inv_eq_of_mul_eq_one_right trM_mul_self]
    exact (s16c11_case5_trM_conj_lr _ _).symm
  · intro hy
    rw [s16c11_case5_Omega, MonoidHom.mem_range] at hy ⊢
    obtain ⟨⟨g, h⟩, hgh⟩ := hy
    refine ⟨(h, g), ?_⟩
    show lr (Matrix.SpecialLinearGroup.toGL h) (Matrix.SpecialLinearGroup.toGL g) = y
    rw [rho_apply] at hgh
    simp only [Prod.fst, Prod.snd] at hgh
    rw [← s16c11_case5_trM_conj_lr (Matrix.SpecialLinearGroup.toGL g)
      (Matrix.SpecialLinearGroup.toGL h), hgh]
    calc (trM : MulAut (VM K)) * (trM * y * trM⁻¹) * trM
        = (trM * trM) * y * (trM⁻¹ * trM) := by group
      _ = y := by rw [trM_mul_self, inv_mul_cancel, one_mul, mul_one]

theorem s16c11_case5_Omega_le_lrRange :
    s16c11_case5_Omega (K := K) ≤ s16c11_case5_lrRange (K := K) := by
  rintro x ⟨⟨g, h⟩, rfl⟩
  exact s16c11_case5_mem_lrRange.mpr
    ⟨Matrix.SpecialLinearGroup.toGL g, Matrix.SpecialLinearGroup.toGL h, rfl⟩

theorem s16c11_case5_lrRange_le_centralizer :
    s16c11_case5_lrRange (K := K) ≤
      Subgroup.centralizer (s16c11C5Scal K : Set (MulAut (VM K))) := by
  intro x hx
  rw [s16c11_case5_mem_lrRange] at hx
  obtain ⟨A, B, rfl⟩ := hx
  exact s16c11_case5_lr_mem_centralizer_scal A B

theorem s16c11_case5_S0_le_N1 :
    s16c11_case5_S0 (K := K) ≤ s16c11_case5_N1 (K := K) := by
  rw [s16c11_case5_S0]
  refine sup_le ?_ ?_
  · refine le_inf ?_ ?_
    · exact (s16c11_case5_V_le_range.trans Subgroup.le_normalizer)
    · exact ((s16c11_case5_V_le_range.trans s16c11_case5_Omega_le_lrRange).trans
        s16c11_case5_lrRange_le_centralizer)
  · rw [Subgroup.zpowers_le, s16c11_case5_N1]
    exact ⟨s16c11_case5_trM_mem_normalizer, s16c11_case5_trM_mem_centralizer_scal⟩

theorem s16c11_case5_N1_le (h4 : 4 ≤ Nat.card K) :
    s16c11_case5_N1 ≤ s16c11_case5_lrRange ⊔ Subgroup.zpowers (s16c11_case5_sigma (K := K)) := by
  intro x hx
  rw [s16c11_case5_N1, Subgroup.mem_inf] at hx
  obtain ⟨hxN, hxC⟩ := hx
  obtain ⟨A, B, τ, hAB⟩ := exists_eq_of_mem_normalizer (K := K) h4 hxN
  obtain hτ := s16c11_case5_frM_eq_one hxC hAB
  subst hτ
  rw [s16c11_case5_frM_one] at hAB
  rcases hAB with h | h
  · rw [h, mul_one]
    exact Subgroup.mem_sup_left (s16c11_case5_mem_lrRange.mpr ⟨A, B, rfl⟩)
  · rw [h, mul_one]
    exact mul_mem (Subgroup.mem_sup_left (s16c11_case5_mem_lrRange.mpr ⟨A, B, rfl⟩))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers (s16c11_case5_sigma (K := K))))

end Normalizer

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
