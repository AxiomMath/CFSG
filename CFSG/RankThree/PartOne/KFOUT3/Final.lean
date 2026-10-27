module

public import CFSG.RankThree.PartOne.KFOUT3.Cocycle
public import CFSG.RankThree.PartOne.KFOUT3.Std

public section

namespace CFSG.RankThree.PartOne.KFOUT3

variable {K : Type} [Field K]

@[expose] noncomputable def semilinMat' (g : GL (Fin 3) K) (σ : K ≃+* K) (e : Bool)
    (x : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 3) (Fin 3) K :=
  (g : Matrix (Fin 3) (Fin 3) K) * ((if e then Matrix.transpose x⁻¹ else x).map σ) *
    ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

theorem coe_inv_eq_matrix_inv (x : SL3 K) :
    ((x⁻¹ : SL3 K) : Matrix (Fin 3) (Fin 3) K) = ((x : Matrix (Fin 3) (Fin 3) K))⁻¹ := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.inv_def, x.det_coe, Ring.inverse_one, one_smul]

@[expose] def gT (D : GL (Fin 3) K) : GL (Fin 3) K :=
  ⟨Matrix.transpose ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
    Matrix.transpose (D : Matrix (Fin 3) (Fin 3) K),
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]⟩

theorem coe_gT (D : GL (Fin 3) K) :
    (gT D : Matrix (Fin 3) (Fin 3) K) =
      Matrix.transpose ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := rfl

theorem coe_gT_inv (D : GL (Fin 3) K) :
    ((gT D)⁻¹ : GL (Fin 3) K) = Matrix.transpose (D : Matrix (Fin 3) (Fin 3) K) := rfl

section Assembly

variable [CharP K 2]

theorem coe_permSL_conj (π : Equiv.Perm (Fin 3)) (z : SL3 K) :
    ((permSL π * z * (permSL π)⁻¹ : SL3 K) : Matrix (Fin 3) (Fin 3) K) =
      ((Matrix.SpecialLinearGroup.toGL (permSL π) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (z : Matrix (Fin 3) (Fin 3) K) *
        (((Matrix.SpecialLinearGroup.toGL (permSL π))⁻¹ : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← map_inv]
  rfl

theorem exists_semilin_of_std (Ψ : PSL3 K ≃* PSL3 K) (π : Equiv.Perm (Fin 3)) (ε : Bool)
    (D : GL (Fin 3) K) (σ : K ≃+* K)
    (hΨ : ∀ x : SL3 K, Ψ (QuotientGroup.mk x) =
      cPerm π (gammaPow ε (QuotientGroup.mk (stdHom D σ x)))) :
    ∃ (g : GL (Fin 3) K) (e : Bool), ∀ x : SL3 K, ∃ y : SL3 K,
      (y : Matrix (Fin 3) (Fin 3) K) = semilinMat' g σ e (x : Matrix (Fin 3) (Fin 3) K) ∧
        Ψ (QuotientGroup.mk x) = QuotientGroup.mk y := by
  cases ε
  · refine ⟨Matrix.SpecialLinearGroup.toGL (permSL π) * D, false,
      fun x => ⟨permSL π * stdHom D σ x * (permSL π)⁻¹, ?_, ?_⟩⟩
    · rw [coe_permSL_conj, coe_stdHom]
      simp only [semilinMat', Bool.false_eq_true, ite_false, Units.val_mul, mul_inv_rev,
        Matrix.mul_assoc]
    · rw [hΨ x]
      show cPerm π (QuotientGroup.mk (stdHom D σ x)) = _
      rw [cPerm_mk]
  · refine ⟨Matrix.SpecialLinearGroup.toGL (permSL π) * gT D, true,
      fun x => ⟨permSL π * gam (stdHom D σ x) * (permSL π)⁻¹, ?_, ?_⟩⟩
    · rw [coe_permSL_conj, coe_gam, ← map_inv, coe_stdHom, coe_inv_eq_matrix_inv]
      simp only [semilinMat', ite_true, Units.val_mul, mul_inv_rev, Matrix.mul_assoc,
        Matrix.transpose_mul, Matrix.transpose_map, coe_gT, coe_gT_inv]
    · rw [hΨ x]
      show cPerm π (gamma (QuotientGroup.mk (stdHom D σ x))) = _
      rw [gamma_mk, cPerm_mk]

end Assembly

end CFSG.RankThree.PartOne.KFOUT3
