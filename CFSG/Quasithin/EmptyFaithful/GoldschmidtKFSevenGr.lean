module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFSevenG
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFSevenInn

public section

namespace CFSG.Quasithin.SBd19F

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

theorem det_symGram : (symGram K).det = -4 := by
  simp [symGram, det_fin_three]
  ring

theorem symGram_transpose : (symGram K)ᵀ = symGram K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symGram]

theorem conjAut_dualAut_fixes (M : GL (Fin 3) K) (hMs : (M : Matrix (Fin 3) (Fin 3) K)ᵀ = M)
    (g : SpecialLinearGroup (Fin 3) K)
    (hg : (g : Matrix (Fin 3) (Fin 3) K) * (M : Matrix (Fin 3) (Fin 3) K) *
      (g : Matrix (Fin 3) (Fin 3) K)ᵀ = M) :
    (conjAut 3 K M * dualAut 3 K) (proj 3 K g) = proj 3 K g := by
  rw [MulAut.mul_apply, dualAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose]
  have hGGi : (g : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hGiG : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (g : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have e0 : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (M : Matrix (Fin 3) (Fin 3) K) =
      (M : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)ᵀ := by
    calc ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (M : Matrix _ _ K)
        = ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((g : Matrix (Fin 3) (Fin 3) K) * (M : Matrix (Fin 3) (Fin 3) K) *
            (g : Matrix (Fin 3) (Fin 3) K)ᵀ) := by rw [hg]
      _ = (M : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)ᵀ := by
          rw [← mul_assoc, ← mul_assoc, hGiG, one_mul]
  have e1 : (M : Matrix (Fin 3) (Fin 3) K) *
      ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ =
      (g : Matrix (Fin 3) (Fin 3) K) * (M : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg Matrix.transpose e0
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hMs] at this
    exact this
  calc (M : Matrix (Fin 3) (Fin 3) K) *
        ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *
        ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = (g : Matrix (Fin 3) (Fin 3) K) *
        ((M : Matrix (Fin 3) (Fin 3) K) * ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
        rw [e1, mul_assoc]
    _ = (g : Matrix (Fin 3) (Fin 3) K) := by rw [Units.mul_inv, mul_one]

theorem not_isSolvable_fixedSub_conjAut_dualAut [Finite K] (hK4 : 4 ≤ Nat.card K)
    (h2 : (2 : K) ≠ 0) (A : GL (Fin 3) K) (hAs : (A : Matrix (Fin 3) (Fin 3) K)ᵀ = A) :
    ¬ Group.IsSolvable ↥(SBd18.fixedSub (conjAut 3 K A * dualAut 3 K)) := by
  classical
  have hdetA : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det (A : Matrix (Fin 3) (Fin 3) K)).mp A.isUnit).ne_zero
  obtain ⟨B, hB, hBA⟩ := exists_gram_normal_form h2 (A : Matrix (Fin 3) (Fin 3) K) hAs hdetA
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hMdet : (symGram K).det ≠ 0 := by
    rw [det_symGram]
    exact neg_ne_zero.mpr h4
  let Bg : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero B hB
  let Mg : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (symGram K) hMdet
  let c : Kˣ := Units.mk0 (-(A : Matrix (Fin 3) (Fin 3) K).det) (neg_ne_zero.mpr hdetA)
  have hGL : Bg * A * Matrix.GeneralLinearGroup.inverseTranspose (Bg⁻¹) =
      GeneralLinearGroup.scalar (Fin 3) c * Mg := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul,
      Matrix.GeneralLinearGroup.coe_inverseTranspose, inv_inv]
    change B * (A : Matrix (Fin 3) (Fin 3) K) * Bᵀ =
      Matrix.scalar (Fin 3) (-(A : Matrix (Fin 3) (Fin 3) K).det) * symGram K
    rw [hBA, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, one_mul]
  have htr := standard_automorphism_transport (K := K) (n := 3)
  have hδδ : dualAut 3 K * dualAut 3 K = 1 := htr.2.2.2.1
  have hδc : ∀ X : GL (Fin 3) K, dualAut 3 K * conjAut 3 K X * dualAut 3 K =
      conjAut 3 K (Matrix.GeneralLinearGroup.inverseTranspose X) := htr.2.2.2.2.1
  have hkey : conjAut 3 K Bg * (conjAut 3 K A * dualAut 3 K) * (conjAut 3 K Bg)⁻¹ =
      conjAut 3 K Mg * dualAut 3 K := by
    have h1 : conjAut 3 K Bg * (conjAut 3 K A * dualAut 3 K) * (conjAut 3 K Bg)⁻¹ =
        conjAut 3 K (Bg * A * Matrix.GeneralLinearGroup.inverseTranspose (Bg⁻¹)) *
          dualAut 3 K := by
      rw [map_mul, map_mul, ← hδc (Bg⁻¹), map_inv]
      calc conjAut 3 K Bg * (conjAut 3 K A * dualAut 3 K) * (conjAut 3 K (Bg⁻¹))
          = conjAut 3 K Bg * conjAut 3 K A * (dualAut 3 K * conjAut 3 K (Bg⁻¹)) := by
            rw [map_inv]
            group
        _ = conjAut 3 K Bg * conjAut 3 K A *
            ((dualAut 3 K * conjAut 3 K (Bg⁻¹) * dualAut 3 K) * dualAut 3 K) := by
            rw [mul_assoc (dualAut 3 K * conjAut 3 K (Bg⁻¹)), hδδ, mul_one]
        _ = conjAut 3 K Bg * conjAut 3 K A * (dualAut 3 K * conjAut 3 K (Bg⁻¹) * dualAut 3 K) *
            dualAut 3 K := by rw [mul_assoc (conjAut 3 K Bg * conjAut 3 K A)]
    rw [h1, hGL, map_mul, conjAut_scalar, one_mul]
  have hMs : (Mg : Matrix (Fin 3) (Fin 3) K)ᵀ = Mg := symGram_transpose
  have hnon := not_isSolvable_fixedSub_of_hom hK4 (symHom K)
    (fun h => conjAut_dualAut_fixes Mg hMs _ (symHom_gram h)) symHom_nontrivial
  have hα : (conjAut 3 K Bg)⁻¹ * (conjAut 3 K Mg * dualAut 3 K) * ((conjAut 3 K Bg)⁻¹)⁻¹ =
      conjAut 3 K A * dualAut 3 K := by
    rw [← hkey]
    group
  have := not_isSolvable_fixedSub_conj (conjAut 3 K Bg)⁻¹ _ hnon
  rw [hα] at this
  exact this

end CFSG.Quasithin.SBd19F
