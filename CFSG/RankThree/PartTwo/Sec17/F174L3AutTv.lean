module

public import CFSG.RankThree.PartTwo.Sec15.F153L3KOutNatLin

open scoped MatrixGroups Matrix

public section

namespace CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Tv

open CFSG.RankThree.PartTwo.Sec15.F153L3K.Out.NatI

theorem funext_fin3 {F : Type} {x y : Fin 3 → F} (h0 : x 0 = y 0) (h1 : x 1 = y 1)
    (h2 : x 2 = y 2) : x = y := by
  funext k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2

theorem tvM_inj {F : Type} [Field F] {φ v φ' v' : Fin 3 → F} (hφ : φ ≠ 0) (hv : v ≠ 0)
    (hφ' : φ' ≠ 0) (hv' : v' ≠ 0) (h : tvM φ v = tvM φ' v') :
    ∃ c : F, c ≠ 0 ∧ v' = c • v ∧ φ = c • φ' := by
  have key : ∀ u : Fin 3 → F, (φ ⬝ᵥ u) • v = (φ' ⬝ᵥ u) • v' := by
    intro u
    have h' : tvM φ v *ᵥ u = tvM φ' v' *ᵥ u := by rw [h]
    rw [tvM_mulVec, tvM_mulVec] at h'
    exact add_left_cancel h'
  have hent : ∀ a b, v a * φ b = v' a * φ' b := by
    intro a b
    have hb := congrFun (key (Pi.single b 1)) a
    simp only [dotProduct_single, mul_one, Pi.smul_apply, smul_eq_mul] at hb
    linear_combination hb
  obtain ⟨j, hj⟩ : ∃ j, φ j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ (funext hcon)
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (funext hcon)
  have hj' : φ' j ≠ 0 := by
    intro h0
    have h1 := hent i j
    rw [h0, mul_zero] at h1
    exact hi ((mul_eq_zero.1 h1).resolve_right hj)
  have hvi : ∀ a, v' a = φ j / φ' j * v a := by
    intro a
    rw [div_mul_eq_mul_div, eq_div_iff hj']
    linear_combination (-1 : F) * hent a j
  refine ⟨φ j / φ' j, div_ne_zero hj hj', funext fun a => ?_, funext fun b => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact hvi a
  · simp only [Pi.smul_apply, smul_eq_mul]
    refine mul_left_cancel₀ hi ?_
    rw [hent i b, hvi i]
    ring

theorem vecMulVec_mulVec3 {F : Type} [Field F] (φ v w : Fin 3 → F) :
    Matrix.vecMulVec v φ *ᵥ w = (φ ⬝ᵥ w) • v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_three]
  ring

theorem tvM_eq {F : Type} [Field F] (φ v : Fin 3 → F) :
    tvM φ v = 1 + Matrix.vecMulVec v φ := by
  have key : ∀ w : Fin 3 → F, tvM φ v *ᵥ w = (1 + Matrix.vecMulVec v φ) *ᵥ w := by
    intro w
    rw [tvM_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec3]
  ext i j
  have hk := congrFun (key (Pi.single j 1)) i
  have e1 : (tvM φ v *ᵥ Pi.single j 1) i = tvM φ v i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have e2 : ((1 + Matrix.vecMulVec v φ) *ᵥ Pi.single j 1) i = (1 + Matrix.vecMulVec v φ) i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← e1, ← e2]
  exact hk

theorem conj_tvM {F : Type} [Field F] (B : GL (Fin 3) F) (φ v : Fin 3 → F) :
    (B : Matrix (Fin 3) (Fin 3) F) * tvM φ v * ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      tvM (φ ᵥ* ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
        ((B : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
  have hBB : (B : Matrix (Fin 3) (Fin 3) F) * ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
    Units.mul_inv B
  simp only [tvM_eq]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hBB, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul]

theorem transpose_tvM {F : Type} [Field F] (φ v : Fin 3 → F) :
    (tvM φ v).transpose = tvM v φ := by
  simp only [tvM_eq]
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_vecMulVec]

theorem tvM_mul_self {F : Type} [Field F] [CharP F 2] {φ v : Fin 3 → F} (h : φ ⬝ᵥ v = 0) :
    tvM φ v * tvM φ v = 1 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hX : Matrix.vecMulVec v φ * Matrix.vecMulVec v φ = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, h, zero_smul, Matrix.vecMulVec_zero]
  have hD : Matrix.vecMulVec v φ + Matrix.vecMulVec v φ = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
    linear_combination (v i * φ j) * h2
  have expand : (1 + Matrix.vecMulVec v φ) * (1 + Matrix.vecMulVec v φ) =
      1 + (Matrix.vecMulVec v φ + Matrix.vecMulVec v φ) +
        Matrix.vecMulVec v φ * Matrix.vecMulVec v φ := by
    noncomm_ring
  rw [tvM_eq, expand, hD, hX, add_zero, add_zero]

theorem cross_rel3 {F : Type} [Field F] {v w x : Fin 3 → F} (h1 : x ⬝ᵥ v = 0)
    (h2 : x ⬝ᵥ w = 0) :
    x 1 * (v 0 * w 1 - v 1 * w 0) = x 2 * (v 2 * w 0 - v 0 * w 2) ∧
      x 2 * (v 1 * w 2 - v 2 * w 1) = x 0 * (v 0 * w 1 - v 1 * w 0) ∧
      x 0 * (v 2 * w 0 - v 0 * w 2) = x 1 * (v 1 * w 2 - v 2 * w 1) := by
  simp only [dotProduct, Fin.sum_univ_three] at h1 h2
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (v 0) * h2 - (w 0) * h1
  · linear_combination (v 1) * h2 - (w 1) * h1
  · linear_combination (v 2) * h2 - (w 2) * h1

theorem cross_scalar3 {F : Type} [Field F] {x : Fin 3 → F} {b0 b1 b2 : F}
    (hb : b0 ≠ 0 ∨ b1 ≠ 0 ∨ b2 ≠ 0)
    (hx0 : x 1 * b2 = x 2 * b1) (hx1 : x 2 * b0 = x 0 * b2) (hx2 : x 0 * b1 = x 1 * b0) :
    ∃ l : F, x 0 = l * b0 ∧ x 1 = l * b1 ∧ x 2 = l * b2 := by
  rcases hb with hb0 | hb1 | hb2
  · refine ⟨x 0 / b0, (div_mul_cancel₀ _ hb0).symm, ?_, ?_⟩
    · rw [div_mul_eq_mul_div, eq_div_iff hb0]
      linear_combination (-1 : F) * hx2
    · rw [div_mul_eq_mul_div, eq_div_iff hb0]
      linear_combination hx1
  · refine ⟨x 1 / b1, ?_, (div_mul_cancel₀ _ hb1).symm, ?_⟩
    · rw [div_mul_eq_mul_div, eq_div_iff hb1]
      linear_combination hx2
    · rw [div_mul_eq_mul_div, eq_div_iff hb1]
      linear_combination (-1 : F) * hx0
  · refine ⟨x 2 / b2, ?_, ?_, (div_mul_cancel₀ _ hb2).symm⟩
    · rw [div_mul_eq_mul_div, eq_div_iff hb2]
      linear_combination (-1 : F) * hx1
    · rw [div_mul_eq_mul_div, eq_div_iff hb2]
      linear_combination hx0

theorem parallel_of_cross3 {F : Type} [Field F] {x y : Fin 3 → F} {b0 b1 b2 : F}
    (hx : x ≠ 0) (hb : b0 ≠ 0 ∨ b1 ≠ 0 ∨ b2 ≠ 0)
    (hx0 : x 1 * b2 = x 2 * b1) (hx1 : x 2 * b0 = x 0 * b2) (hx2 : x 0 * b1 = x 1 * b0)
    (hy0 : y 1 * b2 = y 2 * b1) (hy1 : y 2 * b0 = y 0 * b2) (hy2 : y 0 * b1 = y 1 * b0) :
    ∃ c : F, y = c • x := by
  obtain ⟨l, hl0, hl1, hl2⟩ := cross_scalar3 hb hx0 hx1 hx2
  obtain ⟨m, hm0, hm1, hm2⟩ := cross_scalar3 hb hy0 hy1 hy2
  have hl : l ≠ 0 := by
    rintro rfl
    apply hx
    apply funext_fin3 <;> simp [hl0, hl1, hl2]
  refine ⟨m / l, funext_fin3 ?_ ?_ ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [hm0, hl0]
    field_simp
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [hm1, hl1]
    field_simp
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [hm2, hl2]
    field_simp

theorem orth_of_commute_tvM {F : Type} [Field F] {φ v φ' v' : Fin 3 → F} (hφ : φ ≠ 0) (hv : v ≠ 0)
    (hφ' : φ' ≠ 0) (hv' : v' ≠ 0) (h : φ ⬝ᵥ v = 0) (h' : φ' ⬝ᵥ v' = 0)
    (hc : tvM φ v * tvM φ' v' = tvM φ' v' * tvM φ v) : φ ⬝ᵥ v' = 0 ∧ φ' ⬝ᵥ v = 0 := by
  have K : ∀ u : Fin 3 → F,
      ((φ' ⬝ᵥ u) * (φ ⬝ᵥ v')) • v = ((φ ⬝ᵥ u) * (φ' ⬝ᵥ v)) • v' := by
    intro u
    have e : tvM φ v *ᵥ (tvM φ' v' *ᵥ u) = tvM φ' v' *ᵥ (tvM φ v *ᵥ u) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc]
    funext k
    have ek := congrFun e k
    simp only [tvM_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, Pi.add_apply,
      Pi.smul_apply] at ek
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination ek
  have hab : (φ ⬝ᵥ v') * (φ' ⬝ᵥ v) = 0 := by
    have hK := K v'
    rw [h', zero_mul, zero_smul] at hK
    exact (smul_eq_zero.1 hK.symm).resolve_right hv'
  constructor
  · by_contra ha
    have hb : φ' ⬝ᵥ v = 0 := (mul_eq_zero.1 hab).resolve_left ha
    apply hφ'
    have hu : ∀ u : Fin 3 → F, φ' ⬝ᵥ u = 0 := by
      intro u
      have hK := K u
      rw [hb, mul_zero, zero_smul] at hK
      exact (mul_eq_zero.1 ((smul_eq_zero.1 hK).resolve_right hv)).resolve_right ha
    funext j
    have hj := hu (Pi.single j 1)
    rw [dotProduct_single, mul_one] at hj
    exact hj
  · by_contra hb
    have ha : φ ⬝ᵥ v' = 0 := (mul_eq_zero.1 hab).resolve_right hb
    apply hφ
    funext j
    have hK := K (Pi.single j 1)
    rw [ha, mul_zero, zero_smul] at hK
    have hK' := (mul_eq_zero.1 ((smul_eq_zero.1 hK.symm).resolve_right hv')).resolve_right hb
    rw [dotProduct_single, mul_one] at hK'
    exact hK'

theorem parallel_of_orth_three {F : Type} [Field F] {v w φ ψ : Fin 3 → F} (hv : v ≠ 0)
    (hw : ∀ c : F, w ≠ c • v) (hφ : φ ≠ 0) (hψ : ψ ≠ 0) (h1 : φ ⬝ᵥ v = 0) (h2 : φ ⬝ᵥ w = 0)
    (h3 : ψ ⬝ᵥ v = 0) (h4 : ψ ⬝ᵥ w = 0) : ∃ c : F, ψ = c • φ := by
  obtain ⟨e0, e1, e2⟩ := cross_rel3 h1 h2
  obtain ⟨f0, f1, f2⟩ := cross_rel3 h3 h4
  have hb : v 1 * w 2 - v 2 * w 1 ≠ 0 ∨ v 2 * w 0 - v 0 * w 2 ≠ 0 ∨
      v 0 * w 1 - v 1 * w 0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hb0, hb1, hb2⟩ := hcon
    have hbv : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
      by_contra hcv
      push Not at hcv
      exact hv (funext_fin3 hcv.1 hcv.2.1 hcv.2.2)
    obtain ⟨c, hc⟩ := parallel_of_cross3 (y := w) hv hbv (by ring) (by ring) (by ring)
      (by linear_combination (-1 : F) * hb0) (by linear_combination (-1 : F) * hb1)
      (by linear_combination (-1 : F) * hb2)
    exact hw c hc
  obtain ⟨c, hc⟩ := parallel_of_cross3 hφ hb e0 e1 e2 f0 f1 f2
  exact ⟨c, hc⟩

end CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Tv
