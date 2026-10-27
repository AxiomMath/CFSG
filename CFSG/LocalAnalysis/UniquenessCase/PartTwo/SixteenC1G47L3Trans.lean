module

public import CFSG.RankThree.SubgroupLists.SL3Involutions
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47L3Cls

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped MatrixGroups Matrix

private def l3x1 (F : Type) [Field F] : SL(3, F) :=
  ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

private def l3x2 (F : Type) [Field F] : SL(3, F) :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

private def l3w (F : Type) [Field F] : SL(3, F) :=
  ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

private lemma l3x1_sq (F : Type) [Field F] : l3x1 F * l3x1 F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [l3x1, Matrix.mul_fin_three, Matrix.one_fin_three]

private lemma l3x2_sq (F : Type) [Field F] : l3x2 F * l3x2 F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [l3x2, Matrix.mul_fin_three, Matrix.one_fin_three]

private lemma l3w_sq (F : Type) [Field F] : l3w F * l3w F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [l3w, Matrix.mul_fin_three, Matrix.one_fin_three]

private lemma l3x1_ne_one (F : Type) [Field F] (h2 : (2 : F) ≠ 0) : l3x1 F ≠ 1 := by
  intro h
  have h11 := congrArg (fun y : SL(3, F) => ((y : Matrix (Fin 3) (Fin 3) F)) 1 1) h
  simp [l3x1] at h11
  exact h2 (by linear_combination -h11)

private lemma l3x2_ne_one (F : Type) [Field F] : l3x2 F ≠ 1 := by
  intro h
  have h00 := congrArg (fun y : SL(3, F) => ((y : Matrix (Fin 3) (Fin 3) F)) 0 0) h
  simp [l3x2] at h00

private lemma l3w_ne_one (F : Type) [Field F] (h2 : (2 : F) ≠ 0) : l3w F ≠ 1 := by
  intro h
  have h00 := congrArg (fun y : SL(3, F) => ((y : Matrix (Fin 3) (Fin 3) F)) 0 0) h
  simp [l3w] at h00
  exact h2 (by linear_combination -h00)

private lemma l3x1x2_coe (F : Type) [Field F] :
    ((l3x1 F * l3x2 F : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [l3x1, l3x2, Matrix.mul_fin_three]

private lemma l3x1x2_sq (F : Type) [Field F] :
    (l3x1 F * l3x2 F) ^ 2 = l3w F := by
  apply Subtype.ext
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul]
  simp only [l3x1x2_coe]
  rw [Matrix.mul_fin_three]
  simp [l3w]

private lemma l3_conj_of_gl_conj {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5)
    {u v : SL(3, F)} {N : GL (Fin 3) F}
    (hu : ∃ P : GL (Fin 3) F, P⁻¹ * Matrix.SpecialLinearGroup.toGL u * P = N)
    (hv : ∃ Q : GL (Fin 3) F, Q⁻¹ * Matrix.SpecialLinearGroup.toGL v * Q = N) :
    ∃ a : SL(3, F), a * u * a⁻¹ = v := by
  obtain ⟨P, hP⟩ := hu
  obtain ⟨Q, hQ⟩ := hv
  obtain ⟨a, ha⟩ := s16c1_G47_gl_scale hF (Q * P⁻¹)
  refine ⟨a, ?_⟩
  have hv_eq : Matrix.SpecialLinearGroup.toGL v =
      (Q * P⁻¹) * Matrix.SpecialLinearGroup.toGL u * (Q * P⁻¹)⁻¹ := by
    calc Matrix.SpecialLinearGroup.toGL v
        = Q * N * Q⁻¹ := by rw [← hQ]; group
      _ = Q * (P⁻¹ * Matrix.SpecialLinearGroup.toGL u * P) * Q⁻¹ := by rw [← hP]
      _ = (Q * P⁻¹) * Matrix.SpecialLinearGroup.toGL u * (Q * P⁻¹)⁻¹ := by group
  have hv_m := congrArg (fun y : GL (Fin 3) F => (y : Matrix (Fin 3) (Fin 3) F)) hv_eq
  apply Subtype.ext
  rw [ha u]
  simpa only [Units.val_mul, Units.val_inv_eq_inv_val,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using hv_m.symm

theorem s16c1_G47_L3_trans {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5)
    {t : SL(3, F)} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ a b : SL(3, F), orderOf (a * t * a⁻¹ * (b * t * b⁻¹)) = 4 := by
  classical
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h1 : addOrderOf (1 : F) ∣ 5 := hF ▸ addOrderOf_dvd_natCard (1 : F)
    have h2' : addOrderOf (1 : F) ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero (by simpa using h)
    have h3 : addOrderOf (1 : F) = 1 := Nat.dvd_one.mp (by simpa using Nat.dvd_gcd h1 h2')
    exact one_ne_zero (AddMonoid.addOrderOf_eq_one_iff.mp h3)
  have hT2 : Matrix.SpecialLinearGroup.toGL t * Matrix.SpecialLinearGroup.toGL t = 1 := by
    rw [← map_mul, ht, map_one]
  have hT1 : Matrix.SpecialLinearGroup.toGL t ≠ 1 := fun h =>
    ht1 (Matrix.SpecialLinearGroup.toGL_injective (by simpa using h))
  have hTdet : ((Matrix.SpecialLinearGroup.toGL t : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).det = 1 := t.prop
  have hX1sq : Matrix.SpecialLinearGroup.toGL (l3x1 F) *
      Matrix.SpecialLinearGroup.toGL (l3x1 F) = 1 := by
    rw [← map_mul, l3x1_sq, map_one]
  have hX1ne : Matrix.SpecialLinearGroup.toGL (l3x1 F) ≠ 1 := fun h =>
    l3x1_ne_one F h2 (Matrix.SpecialLinearGroup.toGL_injective (by simpa using h))
  have hX1det : ((Matrix.SpecialLinearGroup.toGL (l3x1 F) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).det = 1 := (l3x1 F).prop
  have hX2sq : Matrix.SpecialLinearGroup.toGL (l3x2 F) *
      Matrix.SpecialLinearGroup.toGL (l3x2 F) = 1 := by
    rw [← map_mul, l3x2_sq, map_one]
  have hX2ne : Matrix.SpecialLinearGroup.toGL (l3x2 F) ≠ 1 := fun h =>
    l3x2_ne_one F (Matrix.SpecialLinearGroup.toGL_injective (by simpa using h))
  have hX2det : ((Matrix.SpecialLinearGroup.toGL (l3x2 F) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).det = 1 := (l3x2 F).prop
  obtain ⟨P₀, hP₀⟩ := CFSG.RankThree.SubgroupLists.exists_conj_negDiag3 h2 hT2 hT1 hTdet
  obtain ⟨P₁, hP₁⟩ := CFSG.RankThree.SubgroupLists.exists_conj_negDiag3 h2 hX1sq hX1ne hX1det
  obtain ⟨P₂, hP₂⟩ := CFSG.RankThree.SubgroupLists.exists_conj_negDiag3 h2 hX2sq hX2ne hX2det
  obtain ⟨a₁, ha₁⟩ := l3_conj_of_gl_conj hF ⟨P₀, hP₀⟩ ⟨P₁, hP₁⟩
  obtain ⟨a₂, ha₂⟩ := l3_conj_of_gl_conj hF ⟨P₀, hP₀⟩ ⟨P₂, hP₂⟩
  refine ⟨a₁, a₂, ?_⟩
  rw [ha₁, ha₂]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 := l3x1x2_sq F
  have hwne := l3w_ne_one F h2
  have hz2ne : (l3x1 F * l3x2 F) ^ 2 ≠ 1 := by
    rw [hz2]
    exact hwne
  have hz4 : (l3x1 F * l3x2 F) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hz2, pow_two, l3w_sq]
  have hord : orderOf (l3x1 F * l3x2 F) = 2 ^ (1 + 1) :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa only [pow_one] using hz2ne)
      (by simpa only [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num] using hz4)
  simpa only [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num] using hord

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
