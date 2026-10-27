module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5TorusC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H.Om4 Matrix

variable {K : Type} [Field K] [Finite K]

private theorem s16c11_case5_matrix_inv_mul (A : GL (Fin 2) K) :
    (A : Matrix (Fin 2) (Fin 2) K)⁻¹ * (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
  have h := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K))
    (inv_mul_cancel A)
  simpa [Units.val_mul, Units.val_inv_eq_inv_val] using h

private theorem s16c11_case5_scalar_transpose (c : Kˣ) :
    (((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) K)) :
      Matrix (Fin 2) (Fin 2) K)ᵀ =
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  simp [Matrix.transpose_apply, Matrix.diagonal_apply, eq_comm]

private theorem s16c11_case5_matrix_scalar_central (u : Kˣ) (X : Matrix (Fin 2) (Fin 2) K) :
    X * (Matrix.GeneralLinearGroup.scalar (Fin 2) u : Matrix (Fin 2) (Fin 2) K) =
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u : Matrix (Fin 2) (Fin 2) K) * X := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem s16c11_case5_lr_scalar_inv (c : Kˣ) :
    lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
       (Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹) = 1 := by
  refine MulEquiv.ext fun X => Multiplicative.toAdd.injective ?_
  rw [toAdd_lr, MulAut.one_apply, s16c11_case5_scalar_transpose c⁻¹,
    ← s16c11_case5_matrix_scalar_central c (Multiplicative.toAdd X)]
  rw [Matrix.mul_assoc, ← Units.val_mul,
    ← MonoidHom.map_mul (Matrix.GeneralLinearGroup.scalar (Fin 2)) c c⁻¹,
    mul_inv_cancel, map_one, Units.val_one, Matrix.mul_one]

private noncomputable def s16c11_case5_scalPair :
    Kˣ →* GL (Fin 2) K × GL (Fin 2) K where
  toFun c := (Matrix.GeneralLinearGroup.scalar (Fin 2) c,
              Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹)
  map_one' := by simp
  map_mul' c d := by
    have h : (c * d)⁻¹ = c⁻¹ * d⁻¹ := by rw [_root_.mul_inv_rev, mul_comm]
    simp [h, map_mul]

private theorem s16c11_case5_scalPair_injective :
    Function.Injective (s16c11_case5_scalPair (K := K)) := by
  intro c d h
  apply Units.ext
  have h1 := congrArg (fun p => (p.1 : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simpa [s16c11_case5_scalPair, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply] using h1

private theorem s16c11_case5_lr_inj_right (A B B' : GL (Fin 2) K)
    (h : lr A B = lr A B') : B = B' := by
  have key : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (A : Matrix (Fin 2) (Fin 2) K) * X * (B : Matrix (Fin 2) (Fin 2) K)ᵀ =
      (A : Matrix (Fin 2) (Fin 2) K) * X * (B' : Matrix (Fin 2) (Fin 2) K)ᵀ := by
    intro X
    have := congrArg (fun f : MulAut (VM K) =>
      Multiplicative.toAdd (f (Multiplicative.ofAdd X))) h
    simpa [toAdd_lr] using this
  have hmul : (A : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K)⁻¹ = 1 := by
    have h := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K))
      (mul_inv_cancel A)
    simpa [Units.val_mul, Units.val_inv_eq_inv_val] using h
  have h1 := key ((A : Matrix (Fin 2) (Fin 2) K)⁻¹)
  simp only [hmul, Matrix.one_mul, Matrix.mul_one] at h1
  exact Units.ext (Matrix.transpose_injective h1)

private theorem s16c11_case5_transpose_eq_inv (A B : GL (Fin 2) K)
    (hAB : (A : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K)ᵀ = 1) :
    (B : Matrix (Fin 2) (Fin 2) K)ᵀ = (A : Matrix (Fin 2) (Fin 2) K)⁻¹ := by
  calc (B : Matrix (Fin 2) (Fin 2) K)ᵀ
      = 1 * (B : Matrix (Fin 2) (Fin 2) K)ᵀ := by rw [Matrix.one_mul]
    _ = ((A : Matrix (Fin 2) (Fin 2) K)⁻¹ * (A : Matrix (Fin 2) (Fin 2) K)) *
        (B : Matrix (Fin 2) (Fin 2) K)ᵀ := by rw [s16c11_case5_matrix_inv_mul A]
    _ = (A : Matrix (Fin 2) (Fin 2) K)⁻¹ *
        ((A : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K)ᵀ) := by
        rw [Matrix.mul_assoc]
    _ = (A : Matrix (Fin 2) (Fin 2) K)⁻¹ := by rw [hAB, Matrix.mul_one]

private theorem s16c11_case5_lrHom_ker_eq :
    (s16c11_case5_lrHom (K := K)).ker = (s16c11_case5_scalPair (K := K)).range := by
  ext p
  constructor
  · intro hp
    rw [MonoidHom.mem_ker] at hp
    obtain ⟨A, B⟩ := p
    rw [MonoidHom.mem_range]
    have key : ∀ X : Matrix (Fin 2) (Fin 2) K,
        (A : Matrix (Fin 2) (Fin 2) K) * X * (B : Matrix (Fin 2) (Fin 2) K)ᵀ = X := by
      intro X
      have h := congrArg (fun f : MulAut (VM K) =>
        Multiplicative.toAdd (f (Multiplicative.ofAdd X))) hp
      simpa [s16c11_case5_lrHom, toAdd_lr] using h
    change lr A B = 1 at hp
    have hAB : (A : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K)ᵀ = 1 := by
      simpa using key 1
    have hBt := s16c11_case5_transpose_eq_inv A B hAB
    have hconv : ∀ C : GL (Fin 2) K, A * C * A⁻¹ = C := by
      intro C
      apply Units.ext
      have h1 := key (C : Matrix (Fin 2) (Fin 2) K)
      rw [hBt] at h1
      simpa [Units.val_mul, Units.val_inv_eq_inv_val] using h1
    have hcenter : A ∈ Subgroup.center (GL (Fin 2) K) := by
      rw [Subgroup.mem_center_iff]
      intro C
      have hAC : A * C = C * A := by
        calc A * C = (A * C * A⁻¹) * A := by group
          _ = C * A := by rw [hconv C]
      exact hAC.symm
    have hrange : A ∈ (Matrix.GeneralLinearGroup.scalar (Fin 2)).range := by
      rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hcenter
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hrange
    have hAc : A = Matrix.GeneralLinearGroup.scalar (Fin 2) c := hc.symm
    have hp' : lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) B =
        lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹) := by
      calc lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c) B
          = lr A B := by rw [← hAc]
        _ = 1 := hp
        _ = lr (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
              (Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹) :=
              (s16c11_case5_lr_scalar_inv c).symm
    have hB : B = Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹ :=
      s16c11_case5_lr_inj_right _ _ _ hp'
    exact ⟨c, by ext <;> simp [s16c11_case5_scalPair, hAc, hB]⟩
  · intro hp
    rw [MonoidHom.mem_range] at hp
    obtain ⟨c, rfl⟩ := hp
    rw [MonoidHom.mem_ker]
    simpa [s16c11_case5_lrHom, s16c11_case5_scalPair] using s16c11_case5_lr_scalar_inv c

private theorem s16c11_case5_trM_ne_lr (A B : GL (Fin 2) K) :
    (trM : MulAut (VM K)) ≠ lr A B := by
  intro h
  have key : ∀ X : Matrix (Fin 2) (Fin 2) K,
      Xᵀ = (A : Matrix (Fin 2) (Fin 2) K) * X * (B : Matrix (Fin 2) (Fin 2) K)ᵀ := by
    intro X
    have hh := congrArg (fun f : MulAut (VM K) =>
      Multiplicative.toAdd (f (Multiplicative.ofAdd X))) h
    simpa [toAdd_trM, toAdd_lr] using hh
  have hAB : (A : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K)ᵀ = 1 := by
    simpa using (key 1).symm
  have hBt := s16c11_case5_transpose_eq_inv A B hAB
  have hconj : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (A : Matrix (Fin 2) (Fin 2) K) * X * (A : Matrix (Fin 2) (Fin 2) K)⁻¹ = Xᵀ := by
    intro X
    have h1 := key X
    rw [hBt] at h1
    exact h1.symm
  set s : Matrix (Fin 2) (Fin 2) K := Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : K) with hs
  set t : Matrix (Fin 2) (Fin 2) K := Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : K) with ht
  have hs00 : sᵀ = s := by rw [hs, Matrix.transpose_single]
  have ht01 : tᵀ = Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : K) := by
    rw [ht, Matrix.transpose_single]
  have hc0 : (A : Matrix (Fin 2) (Fin 2) K) * s * (A : Matrix (Fin 2) (Fin 2) K)⁻¹ = s := by
    rw [hconj, hs00]
  have hEA : (A : Matrix (Fin 2) (Fin 2) K) * s = s * (A : Matrix (Fin 2) (Fin 2) K) := by
    calc (A : Matrix (Fin 2) (Fin 2) K) * s
        = ((A : Matrix (Fin 2) (Fin 2) K) * s * (A : Matrix (Fin 2) (Fin 2) K)⁻¹) *
          (A : Matrix (Fin 2) (Fin 2) K) := by
          rw [show ((A : Matrix (Fin 2) (Fin 2) K) * s * (A : Matrix (Fin 2) (Fin 2) K)⁻¹) *
              (A : Matrix (Fin 2) (Fin 2) K) = (A : Matrix (Fin 2) (Fin 2) K) * s by
            rw [show ((A : Matrix (Fin 2) (Fin 2) K) * s * (A : Matrix (Fin 2) (Fin 2) K)⁻¹) *
                (A : Matrix (Fin 2) (Fin 2) K) =
                (A : Matrix (Fin 2) (Fin 2) K) * s *
                ((A : Matrix (Fin 2) (Fin 2) K)⁻¹ * (A : Matrix (Fin 2) (Fin 2) K)) by
              noncomm_ring]
            rw [s16c11_case5_matrix_inv_mul A, Matrix.mul_one]]
      _ = s * (A : Matrix (Fin 2) (Fin 2) K) := by rw [hc0]
  have hA10 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hEA
    simpa [hs, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply] using this
  have hc1 : (A : Matrix (Fin 2) (Fin 2) K) * t * (A : Matrix (Fin 2) (Fin 2) K)⁻¹ =
      Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : K) := by
    rw [hconj, ht01]
  have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hc1
  simpa [ht, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, hA10] using this

private theorem s16c11_case5_conj_mem_Omega (A B : GL (Fin 2) K) {y : MulAut (VM K)}
    (hy : y ∈ s16c11_case5_Omega (K := K)) :
    lr A B * y * (lr A B)⁻¹ ∈ s16c11_case5_Omega (K := K) := by
  unfold s16c11_case5_Omega at hy ⊢
  rw [MonoidHom.mem_range] at hy ⊢
  obtain ⟨⟨g, h⟩, rfl⟩ := hy
  rw [rho_apply, lr_mul, lr_inv, lr_mul]
  refine ⟨(⟨((A * Matrix.SpecialLinearGroup.toGL g * A⁻¹ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K), ?_⟩,
    ⟨((B * Matrix.SpecialLinearGroup.toGL h * B⁻¹ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K), ?_⟩), ?_⟩
  · have hval : (((A * Matrix.SpecialLinearGroup.toGL g * A⁻¹ : GL (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K) =
        (A : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) *
        ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      simp [Units.val_mul]
    rw [hval, Matrix.det_units_conj A (g : Matrix (Fin 2) (Fin 2) K)]
    exact g.prop
  · have hval : (((B * Matrix.SpecialLinearGroup.toGL h * B⁻¹ : GL (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K) =
        (B : Matrix (Fin 2) (Fin 2) K) * (h : Matrix (Fin 2) (Fin 2) K) *
        ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      simp [Units.val_mul]
    rw [hval, Matrix.det_units_conj B (h : Matrix (Fin 2) (Fin 2) K)]
    exact h.prop
  · rw [rho_apply]
    congr 1
    · exact Units.ext rfl
    · exact Units.ext rfl

theorem s16c11_case5_lrHom_ker_card :
    Nat.card ↥(s16c11_case5_lrHom (K := K)).ker = Nat.card Kˣ := by
  rw [s16c11_case5_lrHom_ker_eq, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (s16c11_case5_scalPair_injective (K := K))]
  exact Subgroup.card_top

theorem s16c11_case5_card_lrRange (hK : Nat.card K = 4) :
    Nat.card ↥(s16c11_case5_lrRange (K := K)) = 10800 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hGL : Nat.card (GL (Fin 2) K) = 180 := by
    have hcard : Fintype.card K = 4 := by
      rw [← Nat.card_eq_fintype_card]
      exact hK
    rw [Matrix.card_GL_field]
    simp [hcard, Fin.prod_univ_two]
  have hunits : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have hcard := Subgroup.card_ker_mul_card_range (s16c11_case5_lrHom (K := K))
  rw [s16c11_case5_lrHom_ker_card, hunits, Nat.card_prod, hGL] at hcard
  norm_num at hcard
  rw [s16c11_case5_lrRange]
  refine Nat.mul_left_cancel (by norm_num : (0 : ℕ) < 3) ?_
  norm_num
  exact hcard

theorem s16c11_case5_trM_not_mem_lrRange :
    (trM : MulAut (VM K)) ∉ s16c11_case5_lrRange (K := K) := by
  rw [s16c11_case5_mem_lrRange]
  rintro ⟨A, B, h⟩
  exact s16c11_case5_trM_ne_lr A B h

theorem s16c11_case5_lrRange_le_normalizer :
    s16c11_case5_lrRange (K := K) ≤
      Subgroup.normalizer (s16c11_case5_Omega (K := K) : Set (MulAut (VM K))) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨A, B, rfl⟩ := s16c11_case5_mem_lrRange.mp hx
    exact s16c11_case5_conj_mem_Omega A B hy
  · intro hy
    obtain ⟨A, B, rfl⟩ := s16c11_case5_mem_lrRange.mp hx
    have h2 := s16c11_case5_conj_mem_Omega A⁻¹ B⁻¹ hy
    have hz : (lr A⁻¹ B⁻¹ : MulAut (VM K)) * (lr A B * y * (lr A B)⁻¹) *
        (lr A⁻¹ B⁻¹ : MulAut (VM K))⁻¹ = y := by
      rw [show (lr A⁻¹ B⁻¹ : MulAut (VM K)) = (lr A B)⁻¹ by rw [lr_inv]]
      rw [inv_inv]
      group
    rw [hz] at h2
    exact h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
