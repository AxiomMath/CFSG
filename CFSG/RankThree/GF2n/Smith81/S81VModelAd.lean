module

public import CFSG.RankThree.GF2n.Smith81.S81VModelU

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] {σ : F ≃+* F} {K : Type} [Field K]

theorem cT_conj (hσ : ∀ c, σ (σ c) = c) (A : Matrix (Fin 3) (Fin 3) F) {H : Matrix (Fin 3) (Fin 3) F}
    (hH : cT σ H = H) : cT σ (A * H * cT σ A) = A * H * cT σ A := by
  rw [cT_mul, cT_cT hσ, cT_mul, hH, Matrix.mul_assoc]

@[expose] noncomputable def adEquiv (e₀ : K ≃+* Fσ σ) (hσ : ∀ c, σ (σ c) = c)
    (A : Matrix (Fin 3) (Fin 3) F) (hA : A.det ≠ 0) : HermK σ e₀ ≃ₗ[K] HermK σ e₀ where
  toFun H := HermK.mk σ e₀ (A * H.mat * cT σ A) (cT_conj hσ A H.cT_mat)
  map_add' H H' := by
    apply HermK.ext
    simp only [HermK.mat_mk, HermK.mat_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c H := by
    apply HermK.ext
    simp only [HermK.mat_mk, HermK.mat_smul, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]
  invFun H := HermK.mk σ e₀ (A⁻¹ * H.mat * cT σ A⁻¹) (cT_conj hσ A⁻¹ H.cT_mat)
  left_inv H := by
    have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
    have h1 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hu
    have hc1 : cT σ A * cT σ A⁻¹ = 1 := by rw [← cT_mul, h1, cT_one]
    apply HermK.ext
    simp only [HermK.mat_mk]
    calc A⁻¹ * (A * H.mat * cT σ A) * cT σ A⁻¹
        = (A⁻¹ * A) * H.mat * (cT σ A * cT σ A⁻¹) := by simp only [Matrix.mul_assoc]
      _ = H.mat := by rw [h1, hc1, Matrix.one_mul, Matrix.mul_one]
  right_inv H := by
    have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
    have h2 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hu
    have hc2 : cT σ A⁻¹ * cT σ A = 1 := by rw [← cT_mul, h2, cT_one]
    apply HermK.ext
    simp only [HermK.mat_mk]
    calc A * (A⁻¹ * H.mat * cT σ A⁻¹) * cT σ A
        = (A * A⁻¹) * H.mat * (cT σ A⁻¹ * cT σ A) := by simp only [Matrix.mul_assoc]
      _ = H.mat := by rw [h2, hc2, Matrix.one_mul, Matrix.mul_one]

theorem adEquiv_mat (e₀ : K ≃+* Fσ σ) (hσ : ∀ c, σ (σ c) = c) (A : Matrix (Fin 3) (Fin 3) F)
    (hA : A.det ≠ 0) (H : HermK σ e₀) :
    (adEquiv e₀ hσ A hA H).mat = A * H.mat * cT σ A := rfl

theorem adEquiv_entry (e₀ : K ≃+* Fσ σ) (hσ : ∀ c, σ (σ c) = c) (A : Matrix (Fin 3) (Fin 3) F)
    (hA : A.det ≠ 0) (H : HermK σ e₀) :
    (adEquiv e₀ hσ A hA H).mat 0 0 = ∑ i, ∑ j, A 0 i * H.mat i j * σ (A 0 j) := by
  rw [adEquiv_mat, Matrix.mul_apply]
  simp only [Matrix.mul_apply, cT_apply, Finset.sum_mul]
  exact Finset.sum_comm

end CFSG.RankThree.GF2n.Smith81.S81V
