module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRestNonsplit
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism

public section

namespace CFSG.StandardType.LinTwoTv

open Matrix

section Block

variable {F : Type} [Field F] {n e s r : ℕ}

theorem rank_nsMat_sub_one (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) (C : Matrix (Fin e) (Fin e) F)
    (k : Fin s → ℕ) (T : Finset (Fin s)) (h0 : ∀ i ∉ T, C ^ k i = 1)
    (hu : ∀ i ∈ T, IsUnit (C ^ k i - 1)) : (SLNS.nsMat ε C k - 1).rank = e * T.card := by
  classical
  set N : Matrix ((Fin e × Fin s) ⊕ Fin r) ((Fin e × Fin s) ⊕ Fin r) F :=
    SLNS.nsCore C k - 1 with hN
  have h1 : SLNS.nsMat ε C k - 1 = N.submatrix ε ε := by
    ext i j
    simp [hN, SLNS.nsMat, Matrix.one_apply]
  rw [h1, Matrix.rank_submatrix]
  apply le_antisymm
  ·
    set S : Finset ((Fin e × Fin s) ⊕ Fin r) :=
      ((Finset.univ : Finset (Fin e)) ×ˢ T).map ⟨Sum.inl, Sum.inl_injective⟩ with hS
    have hcard : S.card = e * T.card := by
      rw [hS, Finset.card_map, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    rw [← hcard]
    refine Matrix.rank_le_card_of_support_subset N S ?_
    intro x hx
    by_contra hxS
    apply hx
    funext y
    rcases x with ⟨a, i⟩ | x
    · have hiT : i ∉ T := fun hi => hxS (by simp [hS, hi])
      rcases y with ⟨b, j⟩ | y
      · by_cases hij : i = j
        · have hCi : C ^ k j = 1 := hij ▸ h0 i hiT
          simp [hN, SLNS.nsCore, Matrix.blockDiagonal_apply, Matrix.one_apply, hij, hCi]
        · simp [hN, SLNS.nsCore, Matrix.blockDiagonal_apply, Matrix.one_apply, hij]
      · simp [hN, SLNS.nsCore, Matrix.one_apply]
    · rcases y with y | y
      · simp [hN, SLNS.nsCore, Matrix.one_apply]
      · simp [hN, SLNS.nsCore, Matrix.one_apply]
  ·
    set g : Fin e × {i // i ∈ T} → (Fin e × Fin s) ⊕ Fin r := fun p => Sum.inl (p.1, p.2.1)
      with hg
    have hB : N.submatrix g g = Matrix.blockDiagonal fun i : {i // i ∈ T} => C ^ k i.1 - 1 := by
      ext ⟨a, i⟩ ⟨b, j⟩
      by_cases hij : i = j
      · subst hij
        simp [hg, hN, SLNS.nsCore, Matrix.blockDiagonal_apply, Matrix.one_apply]
      · have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
        simp [hg, hN, SLNS.nsCore, Matrix.blockDiagonal_apply, Matrix.one_apply, hij, hij']
    have hdet : (Matrix.blockDiagonal fun i : {i // i ∈ T} => C ^ k i.1 - 1).det ≠ 0 := by
      rw [Matrix.det_blockDiagonal]
      refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (hu i.1 i.2)).ne_zero
    have h2 := Matrix.rank_submatrix_le N g g
    rw [hB, Matrix.rank_of_det_ne_zero hdet] at h2
    simpa [Fintype.card_prod, Fintype.card_coe] using h2

end Block

section Inv

variable {K : Type} [Field K] {d : ℕ}

theorem rank_conj_eq {P Q X : Matrix (Fin d) (Fin d) K} (h : P * Q = 1) (h' : Q * P = 1) :
    (P * X * Q).rank = X.rank := by
  have hP : IsUnit P := ⟨⟨P, Q, h, h'⟩, rfl⟩
  have hQ : IsUnit Q := ⟨⟨Q, P, h', h⟩, rfl⟩
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hQ),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hP)]

@[expose] noncomputable def wtGL (B : GL (Fin d) K) : ℕ := ((B : Matrix (Fin d) (Fin d) K) - 1).rank

theorem wtGL_conj (M B : GL (Fin d) K) : wtGL (M * B * M⁻¹) = wtGL B := by
  have h1 : ((M * B * M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1 =
      (M : Matrix (Fin d) (Fin d) K) * ((B : Matrix (Fin d) (Fin d) K) - 1) *
        ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    have h2 : (M : Matrix (Fin d) (Fin d) K) * ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h2]
    simp only [Units.val_mul]
  rw [wtGL, wtGL, h1]
  exact rank_conj_eq (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])

theorem wtGL_inverseTranspose (B : GL (Fin d) K) :
    wtGL (Matrix.GeneralLinearGroup.inverseTranspose B) = wtGL B := by
  have h1 : ((Matrix.GeneralLinearGroup.inverseTranspose B : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) - 1 =
      (-((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((B : Matrix (Fin d) (Fin d) K) - 1))ᵀ := by
    have h2 : ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        (B : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, Matrix.neg_mul, Matrix.mul_sub, h2,
      Matrix.mul_one, Matrix.transpose_neg, Matrix.transpose_sub, Matrix.transpose_one]
    simp
  rw [wtGL, wtGL, h1, Matrix.rank_transpose]
  have hu : IsUnit (-((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := (B⁻¹).isUnit.neg
  rw [Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]

end Inv

end CFSG.StandardType.LinTwoTv

end
