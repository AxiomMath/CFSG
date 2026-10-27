module

public import CFSG.RankThree.PartTwo.Sec3.Sims321Cong
public import CFSG.RankThree.PartTwo.Sec3.Sims321Companion
public import CFSG.RankThree.PartTwo.Sec3.Sims321Order
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction

public section

namespace CFSG.RankThree.PartTwo.Sec3.Sims321

open scoped MatrixGroups
open Matrix CFSG.ComponentClassification
open CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

private def transposeGL {R : Type*} [CommRing R] (K : GL (Fin 3) R) : GL (Fin 3) R where
  val := (K : Matrix (Fin 3) (Fin 3) R)ᵀ
  inv := ((K⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)ᵀ
  val_inv := by rw [← Matrix.transpose_mul, K.inv_mul, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, K.mul_inv, Matrix.transpose_one]

private theorem coe_transposeGL {R : Type*} [CommRing R] (K : GL (Fin 3) R) :
    (transposeGL K : Matrix (Fin 3) (Fin 3) R) = (K : Matrix (Fin 3) (Fin 3) R)ᵀ := rfl

private theorem coe_inv_transposeGL {R : Type*} [CommRing R] (K : GL (Fin 3) R) :
    ((transposeGL K)⁻¹ : GL (Fin 3) R) = ((K⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)ᵀ :=
  rfl

private theorem symm_conj_aux {R : Type*} [CommRing R] (K Ki C H : Matrix (Fin 3) (Fin 3) R)
    (hKi : Ki * K = 1) (hH : K * Kᵀ = H) (hHC : H * C = Cᵀ * H) :
    (Kᵀ * C * Kiᵀ)ᵀ = Kᵀ * C * Kiᵀ := by
  have h1 : Kᵀ * Kiᵀ = 1 := by rw [← Matrix.transpose_mul, hKi, Matrix.transpose_one]
  have h2 : (Kᵀ * C * Kiᵀ)ᵀ = Ki * Cᵀ * K := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [h2]
  calc Ki * Cᵀ * K = Ki * Cᵀ * K * (Kᵀ * Kiᵀ) := by rw [h1, Matrix.mul_one]
    _ = Ki * (Cᵀ * (K * Kᵀ)) * Kiᵀ := by simp only [Matrix.mul_assoc]
    _ = Ki * (H * C) * Kiᵀ := by rw [hH, hHC]
    _ = Ki * ((K * Kᵀ) * C) * Kiᵀ := by rw [hH]
    _ = (Ki * K) * Kᵀ * C * Kiᵀ := by simp only [Matrix.mul_assoc]
    _ = Kᵀ * C * Kiᵀ := by rw [hKi, Matrix.one_mul]

private theorem graph_conj_aux {R : Type*} [CommRing R] (K Ki z : Matrix (Fin 3) (Fin 3) R)
    (hKi : Ki * K = 1) (hz : zᵀ = z) :
    K * Kᵀ * (K * z * Ki)ᵀ * (Kiᵀ * Ki) = K * z * Ki := by
  have h1 : Kᵀ * Kiᵀ = 1 := by rw [← Matrix.transpose_mul, hKi, Matrix.transpose_one]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hz]
  calc K * Kᵀ * (Kiᵀ * (z * Kᵀ)) * (Kiᵀ * Ki)
      = K * (Kᵀ * Kiᵀ) * z * (Kᵀ * Kiᵀ) * Ki := by simp only [Matrix.mul_assoc]
    _ = K * z * Ki := by rw [h1, Matrix.mul_one, Matrix.mul_one]

private theorem companion3_zero_pow_three {R : Type*} [CommRing R] :
    (companion3 (1 : R) 0 0) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companion3, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

private theorem exists_involution_sl {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R)
    (hdet : M.det = 1) (hM : M * M = 1) (hne : M ≠ 1) :
    ∃ s : SL(3, R), (s : Matrix (Fin 3) (Fin 3) R) = M ∧ s * s = 1 ∧ s ≠ 1 :=
  ⟨⟨M, hdet⟩, rfl, Subtype.ext hM, fun h => hne (congrArg Subtype.val h)⟩

theorem exists_symm_orderOf_prod_three {n : ℕ} (hF : Fintype.card F = 2 ^ n) (hn : 0 < n)
    {r : ℕ} (hr : r.Prime) (hr3 : r ∣ 2 ^ (3 * n) - 1)
    (hrk : ∀ k : ℕ, 0 < k → k < 3 * n → ¬ r ∣ 2 ^ k - 1) :
    ∃ y τ₁ τ₂ τ₃ : SL(3, F), orderOf y = r ∧
      (y : Matrix (Fin 3) (Fin 3) F)ᵀ = (y : Matrix (Fin 3) (Fin 3) F) ∧ y = τ₁ * τ₂ * τ₃ ∧
      τ₁ * τ₁ = 1 ∧ τ₁ ≠ 1 ∧ τ₂ * τ₂ = 1 ∧ τ₂ ≠ 1 ∧ τ₃ * τ₃ = 1 ∧ τ₃ ≠ 1 := by
  have hn1 : ¬ r ∣ 2 ^ n - 1 := hrk n hn (by omega)
  have hn2 : ¬ r ∣ 2 ^ (2 * n) - 1 := hrk (2 * n) (by omega) (by omega)
  have hn3 : ¬ r ∣ 3 := by
    have h := hrk 2 (by omega) (by omega)
    norm_num at h
    exact h
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 2 ^ (3 * n) := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ (3 * n) := Nat.one_le_two_pow
    omega
  have hv : (Pi.single 0 1 : Fin 3 → F) ≠ 0 := fun h => by
    have := congrFun h 0
    simp at this
  obtain ⟨y₁, hy₁⟩ := exists_orderOf_eq_prime hF hr hr3 hn1
  obtain ⟨P, a, b, c, hP⟩ := exists_conj_companion3 _ _
    (linearIndependent_of_orderOf hF hr hr2 hn1 hn2 y₁ hy₁ (Pi.single 0 1) hv)
  have ha : a = 1 := by
    have h := congrArg Matrix.det hP
    rw [Matrix.det_units_conj, det_companion3] at h
    rw [← h]
    exact y₁.2
  subst ha
  obtain ⟨C, hC⟩ : ∃ C : SL(3, F), (C : Matrix (Fin 3) (Fin 3) F) = companion3 1 b c :=
    ⟨⟨companion3 1 b c, det_companion3 1 b c⟩, rfl⟩
  have hord : orderOf C = r := by
    have hy₁C : y₁ = slConjugation 3 F P C :=
      Subtype.ext (by rw [slConjugation_matrix, hC]; exact hP)
    rw [← hy₁, hy₁C, MulEquiv.orderOf_eq]
  have hbc : b ≠ 0 ∨ c ≠ 0 := by
    by_contra hcon
    obtain ⟨hb, hc⟩ := not_or.mp hcon
    obtain rfl := not_not.mp hb
    obtain rfl := not_not.mp hc
    refine hn3 (hord ▸ orderOf_dvd_of_pow_eq_one (Subtype.ext ?_))
    rw [Matrix.SpecialLinearGroup.coe_pow, hC, companion3_zero_pow_three]
    rfl
  obtain ⟨s1, hs1, hsq1, hne1⟩ :=
    exists_involution_sl (R := F) swap12 det_swap12 swap12_mul_self swap12_ne_one
  obtain ⟨s2, hs2, hsq2, hne2⟩ :=
    exists_involution_sl (R := F) swap23 det_swap23 swap23_mul_self swap23_ne_one
  obtain ⟨s3, hs3, hsq3, hne3⟩ :=
    exists_involution_sl (tau3 b c) (det_tau3 b c) (tau3_mul_self b c) (tau3_ne_one hbc)
  have hCs : C = s1 * s2 * s3 := Subtype.ext (by
    rw [hC, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hs1, hs2, hs3,
      companion3_one_eq])
  have hHu : IsUnit (hankel3 b c) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (IsUnit.of_mul_eq_one _ (det_hankel3_mul_self b c))
  obtain ⟨K, hK⟩ := exists_mul_transpose_eq_of_symm hHu.unit
    (by rw [hHu.unit_spec]; exact hankel3_transpose b c)
  rw [hHu.unit_spec] at hK
  obtain ⟨φ, hφ⟩ : ∃ φ : MulAut SL(3, F), ∀ x : SL(3, F),
      (φ x : Matrix (Fin 3) (Fin 3) F) = (transposeGL K : Matrix (Fin 3) (Fin 3) F) * x *
        ((transposeGL K)⁻¹ : GL (Fin 3) F) := ⟨slConjugation 3 F (transposeGL K),
    slConjugation_matrix 3 F (transposeGL K)⟩
  refine ⟨φ C, φ s1, φ s2, φ s3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hord
  · rw [hφ, hC, coe_transposeGL, coe_inv_transposeGL]
    exact symm_conj_aux _ _ _ _ K.inv_mul hK (hankel3_mul_companion3 1 b c)
  · rw [hCs, map_mul, map_mul]
  · rw [← map_mul, hsq1, map_one]
  · exact fun h => hne1 (φ.injective (h.trans (map_one φ).symm))
  · rw [← map_mul, hsq2, map_one]
  · exact fun h => hne2 (φ.injective (h.trans (map_one φ).symm))
  · rw [← map_mul, hsq3, map_one]
  · exact fun h => hne3 (φ.injective (h.trans (map_one φ).symm))

theorem exists_inverted_of_symm {n : ℕ} (hF : Fintype.card F = 2 ^ n) (hn : 0 < n)
    {r : ℕ} (hr : r.Prime) (hr3 : r ∣ 2 ^ (3 * n) - 1)
    (hrk : ∀ k : ℕ, 0 < k → k < 3 * n → ¬ r ∣ 2 ^ k - 1) (B : GL (Fin 3) F)
    (hB : (B : Matrix (Fin 3) (Fin 3) F)ᵀ = B) :
    ∃ g : SL(3, F), orderOf g = r ∧
      CatalogueBHigherLinearAction.slConjugation 3 F B (CatalogueBGraphForm.slGraphAut 3 F g) =
        g⁻¹ := by
  obtain ⟨K, hK⟩ := exists_mul_transpose_eq_of_symm B hB
  obtain ⟨y₀, -, -, -, hy₀r, hy₀s, -⟩ := exists_symm_orderOf_prod_three hF hn hr hr3 hrk
  have hz : (((y₀⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ =
      ((y₀⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_transpose, hy₀s]
  have hBi : ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((K⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ *
        ((K⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have hBL : B = K * transposeGL K := Units.ext hK.symm
    rw [hBL, _root_.mul_inv_rev, Units.val_mul]
    rfl
  have e1 : (((slConjugation 3 F K y₀)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (K : Matrix (Fin 3) (Fin 3) F) * ((y₀⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
        ((K⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← map_inv, slConjugation_matrix]
  refine ⟨slConjugation 3 F K y₀, by rw [MulEquiv.orderOf_eq]; exact hy₀r, ?_⟩
  apply Subtype.ext
  rw [slConjugation_matrix, CatalogueBGraphForm.slGraphAut_matrix, e1, hBi, ← hK]
  exact graph_conj_aux _ _ _ K.inv_mul hz

end CFSG.RankThree.PartTwo.Sec3.Sims321
