module

public import CFSG.GH74.GLS.IVK.L2.FixedSL
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.RankThree.PartTwo.Sec3.OrderThreeFixedPointFreeModule

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.GorensteinWalter CFSG.GH74.GLS.IVK Matrix

theorem trace_eq_neg_one_of_cube {F : Type*} [Field F] {ω : Matrix (Fin 2) (Fin 2) F}
    (hdet : ω.det = 1) (h3ω : ω * ω * ω = 1) (h1 : ω ≠ 1) : ω 0 0 + ω 1 1 = -1 := by
  rw [Matrix.det_fin_two] at hdet
  have e : ∀ i j, (ω * ω * ω) i j = (1 : Matrix (Fin 2) (Fin 2) F) i j := fun i j => by rw [h3ω]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have k01 : ((ω 0 0 + ω 1 1) ^ 2 - 1) * ω 0 1 = 0 := by linear_combination e01 + ω 0 1 * hdet
  have k10 : ((ω 0 0 + ω 1 1) ^ 2 - 1) * ω 1 0 = 0 := by linear_combination e10 + ω 1 0 * hdet
  have k00 : ((ω 0 0 + ω 1 1) ^ 2 - 1) * ω 0 0 - (1 + (ω 0 0 + ω 1 1)) = 0 := by
    linear_combination e00 + (2 * ω 0 0 + ω 1 1) * hdet
  have k11 : ((ω 0 0 + ω 1 1) ^ 2 - 1) * ω 1 1 - (1 + (ω 0 0 + ω 1 1)) = 0 := by
    linear_combination e11 + (ω 0 0 + 2 * ω 1 1) * hdet
  by_cases hτ : (ω 0 0 + ω 1 1) ^ 2 - 1 = 0
  · rw [hτ, zero_mul, zero_sub, neg_eq_zero] at k00
    linear_combination k00
  · exfalso
    have hb := (mul_eq_zero.mp k01).resolve_left hτ
    have hc := (mul_eq_zero.mp k10).resolve_left hτ
    have had : ω 0 0 = ω 1 1 := mul_left_cancel₀ hτ (by linear_combination k00 - k11)
    have ha2 : ω 0 0 * ω 0 0 = 1 := by
      rw [hb, hc, ← had] at hdet
      linear_combination hdet
    rw [← had] at k00
    have ha : ω 0 0 = 1 := by linear_combination k00 - 4 * ω 0 0 * ha2
    apply h1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, ← had]

section Construction

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem map_mul_σ (X Y : Matrix (Fin 2) (Fin 2) K) : (X * Y).map σ = X.map σ * Y.map σ :=
  Matrix.map_mul (f := (σ : K →+* K))

theorem map_one_σ : (1 : Matrix (Fin 2) (Fin 2) K).map σ = 1 :=
  Matrix.map_one σ (map_zero σ) (map_one σ)

theorem det_map_σ (X : Matrix (Fin 2) (Fin 2) K) : (X.map σ).det = σ X.det :=
  ((σ : K →+* K).map_det X).symm

theorem map_smul_σ (c : K) (X : Matrix (Fin 2) (Fin 2) K) : (c • X).map σ = σ c • X.map σ := by
  ext i j
  simp

theorem map_subtype_map_σ (X : Matrix (Fin 2) (Fin 2) (GH74.GLS.IVK.fixedField σ)) :
    (X.map (GH74.GLS.IVK.fixedField σ).subtype).map σ =
      X.map (GH74.GLS.IVK.fixedField σ).subtype := by
  ext i j
  exact GH74.GLS.IVK.fixedField_apply σ (X i j)

theorem exists_map_subtype_eq {X : Matrix (Fin 2) (Fin 2) K} (hX : X.map σ = X) :
    ∃ X₀ : Matrix (Fin 2) (Fin 2) (GH74.GLS.IVK.fixedField σ),
      X₀.map (GH74.GLS.IVK.fixedField σ).subtype = X :=
  ⟨fun i j => ⟨X i j, (GH74.GLS.IVK.mem_fixedField_iff σ _).mpr
    (congrFun (congrFun hX i) j)⟩, rfl⟩

theorem exists_commute_map_eq (h3K : (3 : K) ≠ 0) (hσ : orderOf σ = 3)
    {D : Matrix (Fin 2) (Fin 2) K} (hDdet : D.det = 1) (hD3 : D * D * D = 1) (hD1 : D ≠ 1)
    (hDσ : D.map σ = D) :
    ∃ w : Matrix (Fin 2) (Fin 2) K, w.det = 1 ∧ w * D = D * w ∧ D * D * w.map σ = w := by
  set ι := (GH74.GLS.IVK.fixedField σ).subtype with hι
  have hD3r : ∀ X : Matrix (Fin 2) (Fin 2) K, D * (D * (D * X)) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hD3, Matrix.one_mul]
  have hAi : H90.Ai σ D 3 = 1 := by
    show D * (D * (D * (1 : Matrix (Fin 2) (Fin 2) K).map σ).map σ).map σ = 1
    rw [map_one_σ, Matrix.mul_one, hDσ, map_mul_σ, hDσ, ← Matrix.mul_assoc, hD3]
  obtain ⟨B, hBdet, hB⟩ := H90.speiser σ D 3 hσ (by norm_num) hAi
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBu
  have hBB' : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBu
  have hBBr : ∀ X : Matrix (Fin 2) (Fin 2) K, B * (B⁻¹ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hBB, Matrix.one_mul]
  have hBB'r : ∀ X : Matrix (Fin 2) (Fin 2) K, B⁻¹ * (B * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hBB', Matrix.one_mul]
  have hBσ : B.map σ = D * (D * B) := by
    calc B.map σ = D * (D * (D * B.map σ)) := (hD3r _).symm
      _ = D * (D * B) := by rw [hB]
  have hBiσ : (B⁻¹).map σ = B⁻¹ * D := by
    have h1 : (B⁻¹).map σ * B.map σ = 1 := by rw [← map_mul_σ, hBB', map_one_σ]
    have h2 : B⁻¹ * D * B.map σ = 1 := by
      rw [hBσ, Matrix.mul_assoc, hD3r, hBB']
    rw [← Matrix.inv_eq_left_inv h1, ← Matrix.inv_eq_left_inv h2]
  have hMσ : (B⁻¹ * D * B).map σ = B⁻¹ * D * B := by
    rw [map_mul_σ, map_mul_σ, hBiσ, hDσ, hBσ]
    simp only [Matrix.mul_assoc]
    rw [hD3r]
  have hMdet : (B⁻¹ * D * B).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hDdet, mul_one, ← Matrix.det_mul, hBB', Matrix.det_one]
  have htrD : D 0 0 + D 1 1 = -1 := trace_eq_neg_one_of_cube hDdet hD3 hD1
  have htrM : (B⁻¹ * D * B) 0 0 + (B⁻¹ * D * B) 1 1 = -1 := by
    have h1 : Matrix.trace (B⁻¹ * D * B) = Matrix.trace D := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hBB, Matrix.one_mul]
    rw [Matrix.trace_fin_two, Matrix.trace_fin_two] at h1
    rw [h1, htrD]
  obtain ⟨M₀, hM₀⟩ := exists_map_subtype_eq hMσ
  obtain ⟨D₀, hD₀⟩ := exists_map_subtype_eq hDσ
  have h3₀ : (3 : GH74.GLS.IVK.fixedField σ) ≠ 0 := by
    intro h
    apply h3K
    have h1 := congrArg ι h
    rwa [map_ofNat, map_zero] at h1
  have hdet₀ : ∀ X₀ : Matrix (Fin 2) (Fin 2) (GH74.GLS.IVK.fixedField σ),
      (X₀.map ι).det = 1 → X₀.det = 1 := fun X₀ h => by
    apply ι.injective
    rw [RingHom.map_det, map_one]
    exact h
  have htr₀ : ∀ X₀ : Matrix (Fin 2) (Fin 2) (GH74.GLS.IVK.fixedField σ),
      (X₀.map ι) 0 0 + (X₀.map ι) 1 1 = -1 → X₀ 0 0 + X₀ 1 1 = -1 := fun X₀ h => by
    apply ι.injective
    rw [map_add, map_neg, map_one]
    exact h
  obtain ⟨P₁, Q₁, hPQ₁, hQP₁, hM₁⟩ := Sec3.exists_conj_companion h3₀
    (hdet₀ M₀ (hM₀ ▸ hMdet)) (htr₀ M₀ (hM₀ ▸ htrM))
  obtain ⟨P₂, Q₂, hPQ₂, hQP₂, hD₂⟩ := Sec3.exists_conj_companion h3₀
    (hdet₀ D₀ (hD₀ ▸ hDdet)) (htr₀ D₀ (hD₀ ▸ htrD))
  have hUU₀ : (P₂ * Q₁) * (P₁ * Q₂) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q₁, hQP₁, Matrix.one_mul, hPQ₂]
  have hU'U₀ : (P₁ * Q₂) * (P₂ * Q₁) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q₂, hQP₂, Matrix.one_mul, hPQ₁]
  have hconj₀ : (P₂ * Q₁) * M₀ * (P₁ * Q₂) = D₀ := by
    have e1 : D₀ = P₂ * !![0, -1; 1, -1] * Q₂ := by
      rw [← hD₂, Matrix.mul_assoc, hPQ₂, Matrix.mul_one]
    have hM₁r : ∀ X, M₀ * (P₁ * X) = P₁ * (!![0, -1; 1, -1] * X) := fun X => by
      rw [← Matrix.mul_assoc, hM₁, Matrix.mul_assoc]
    have hQP₁r : ∀ X, Q₁ * (P₁ * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hQP₁, Matrix.one_mul]
    rw [e1]
    simp only [Matrix.mul_assoc]
    rw [hM₁r, hQP₁r]
  set U := (P₂ * Q₁).map ι with hU
  set U' := (P₁ * Q₂).map ι with hU'
  have hUU' : U * U' = 1 := by
    rw [hU, hU', ← Matrix.map_mul, hUU₀, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hU'U : U' * U = 1 := by
    rw [hU, hU', ← Matrix.map_mul, hU'U₀, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hconj : U * (B⁻¹ * D * B) * U' = D := by
    rw [← hM₀, ← hD₀, hU, hU', ← Matrix.map_mul, ← Matrix.map_mul, hconj₀]
  have hU'σ : U'.map σ = U' := by rw [hU']; exact map_subtype_map_σ _
  set z := B * U' with hz
  have hU'D : U' * D = B⁻¹ * D * B * U' := by
    calc U' * D = U' * (U * (B⁻¹ * D * B) * U') := by rw [hconj]
      _ = B⁻¹ * D * B * U' := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU'U, Matrix.one_mul]
  have hzD : z * D = D * z := by
    rw [hz, Matrix.mul_assoc, hU'D]
    simp only [Matrix.mul_assoc]
    rw [hBBr]
  have hzσ : z.map σ = D * (D * z) := by
    rw [hz, map_mul_σ, hU'σ, hBσ]
    simp only [Matrix.mul_assoc]
  have hzdet : z.det ≠ 0 := by
    rw [hz, Matrix.det_mul]
    refine mul_ne_zero hBdet fun h0 => ?_
    have := congrArg Matrix.det hUU'
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  refine ⟨(z.det)⁻¹ • (z * z), ?_, ?_, ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin, show (z * z).det = z.det ^ 2 by
      rw [Matrix.det_mul, pow_two], inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hzdet)]
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, hzD, ← Matrix.mul_assoc, hzD,
      Matrix.mul_assoc]
  · have hzdetσ : σ z.det = z.det := by
      rw [← det_map_σ, hzσ, Matrix.det_mul, Matrix.det_mul, hDdet, one_mul, one_mul]
    have hzD' : ∀ X : Matrix (Fin 2) (Fin 2) K, z * (D * X) = D * (z * X) := fun X => by
      rw [← Matrix.mul_assoc, hzD, Matrix.mul_assoc]
    rw [map_smul_σ, map_inv₀, hzdetσ, map_mul_σ, hzσ, Matrix.mul_smul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [hD3r, hzD', hzD', hD3r]

end Construction

theorem exists_psl_commute_mul_inv_eq_sq {K : Type} [Field K] [Finite K] (h3K : (3 : K) ≠ 0)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) {d : PSL2 K} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hdσ : psl2FieldAut K σ d = d) :
    ∃ x : PSL2 K, x * d = d * x ∧ x * (psl2FieldAut K σ x)⁻¹ = d ^ 2 := by
  have hodd : Odd (orderOf σ) := by rw [hσ]; decide
  obtain ⟨Y, rfl⟩ := QuotientGroup.mk_surjective d
  set φ := Matrix.SpecialLinearGroup.map (n := Fin 2) σ.toRingHom with hφ
  have hmk : ∀ Z : Matrix.SpecialLinearGroup (Fin 2) K,
      psl2FieldAut K σ (QuotientGroup.mk Z : PSL2 K) = QuotientGroup.mk (φ Z) := fun Z => by
    rw [psl2FieldAut_apply]
    exact psl2RingEquiv_mk σ Z
  have hYσ : φ Y = Y := by
    obtain ⟨M₀, hM₀⟩ := exists_map_eq_of_psl_fixed σ hodd Y (by rw [← hmk]; exact hdσ)
    rw [← hM₀]
    ext i j
    exact fixedField_apply σ (M₀ i j)
  have hY3 : Y ^ 3 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [← QuotientGroup.eq_one_iff]
    exact hd3
  obtain ⟨r, hr2, hrY⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hY3
  rw [Fintype.card_fin] at hr2
  have hY6 : Y ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add]
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, ← hrY, Matrix.SpecialLinearGroup.coe_one,
      Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, ← pow_two, hr2, Matrix.diagonal_one]
  set D := Y ^ 4 with hD
  have hD3 : D ^ 3 = 1 := by
    rw [hD, ← pow_mul, show 4 * 3 = 6 * 2 from rfl, pow_mul, hY6, one_pow]
  have hDd : (QuotientGroup.mk D : PSL2 K) = QuotientGroup.mk Y := by
    rw [hD, QuotientGroup.mk_pow, show 4 = 3 + 1 from rfl, pow_succ, hd3, one_mul]
  have hDσ : φ D = D := by rw [hD, map_pow, hYσ]
  have hD1 : D ≠ 1 := by
    intro h1
    apply hd1
    rw [← hDd, h1, QuotientGroup.mk_one]
  have hDdetm : (D : Matrix (Fin 2) (Fin 2) K).det = 1 := Matrix.SpecialLinearGroup.det_coe D
  have hD3m : (D : Matrix (Fin 2) (Fin 2) K) * D * D = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← pow_two,
      ← pow_succ, hD3, Matrix.SpecialLinearGroup.coe_one]
  have hD1m : (D : Matrix (Fin 2) (Fin 2) K) ≠ 1 := fun h =>
    hD1 (Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [h, Matrix.SpecialLinearGroup.coe_one])
  have hDσm : (D : Matrix (Fin 2) (Fin 2) K).map σ = D := by
    have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
      (A : Matrix (Fin 2) (Fin 2) K)) hDσ
    simpa [hφ, Matrix.SpecialLinearGroup.map_apply_coe] using h1
  obtain ⟨w, hwdet, hwD, hwσ⟩ := exists_commute_map_eq h3K hσ hDdetm hD3m hD1m hDσm
  set W : Matrix.SpecialLinearGroup (Fin 2) K := ⟨w, hwdet⟩ with hW
  have hWm : (W : Matrix (Fin 2) (Fin 2) K) = w := rfl
  rw [← hDd]
  refine ⟨QuotientGroup.mk W, ?_, ?_⟩
  · have hWD : W * D = D * W := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hWm, hwD]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hWD]
  · have h1 : D * D * φ W = W := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hφ,
        Matrix.SpecialLinearGroup.map_apply_coe, hWm]
      exact congrFun (congrFun hwσ i) j
    have hWσ : φ W = D⁻¹ * D⁻¹ * W := by
      calc φ W = D⁻¹ * D⁻¹ * (D * D * φ W) := by group
        _ = D⁻¹ * D⁻¹ * W := by rw [h1]
    rw [hmk, hWσ, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    group

end CFSG.RankThree.PartTwo.KFacts
