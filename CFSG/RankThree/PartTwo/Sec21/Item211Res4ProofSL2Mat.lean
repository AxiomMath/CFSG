module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSL2
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofCube
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofCore

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG Matrix
open scoped MatrixGroups

namespace Item211Res4Proof

open Item211Lie3Proof (IsScalar2)

variable {F : Type} [Field F]

theorem mat_cube_eq_one {X : SL(2, F)} (hX3 : X ^ 3 = 1) :
    (X : Matrix (Fin 2) (Fin 2) F) * X * X = 1 := by
  have e := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) hX3
  simpa [pow_succ] using e

theorem sq_add_self_add_one {X : SL(2, F)} (hX3 : X ^ 3 = 1) (hX1 : X ≠ 1) :
    (X : Matrix (Fin 2) (Fin 2) F) * X + X + 1 = 0 :=
  Item228Census3Proof.sl2_sq_add_self_add_one X.2 (mat_cube_eq_one hX3)
    (fun h => hX1 (Subtype.ext h))

theorem trace_eq_neg_one {X : SL(2, F)} (hX3 : X ^ 3 = 1) (hX1 : X ≠ 1) :
    (X : Matrix (Fin 2) (Fin 2) F).trace = -1 :=
  (Item211Lie3Proof.eq_one_or_trace_eq_neg_one X.2 (mat_cube_eq_one hX3)).resolve_left
    (fun h => hX1 (Subtype.ext h))

theorem not_isScalar2_of_cube (h3 : (3 : F) ≠ 0) {X : SL(2, F)} (hX3 : X ^ 3 = 1)
    (hX1 : X ≠ 1) : ¬ IsScalar2 (X : Matrix (Fin 2) (Fin 2) F) :=
  Item211Lie3Proof.not_isScalar2_of_root h3 X.2 (sq_add_self_add_one hX3 hX1)

theorem neg_one_pow_three : (-1 : SL(2, F)) ^ 3 = -1 := by
  apply Subtype.ext
  simp [pow_succ, Matrix.SpecialLinearGroup.coe_neg]

theorem neg_one_mul_comm (B : SL(2, F)) : (-1 : SL(2, F)) * B = B * -1 := by
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_neg]

theorem conj_eq_of_conj_eq_or_neg (h2 : (2 : F) ≠ 0) {X : SL(2, F)} (hX3 : X ^ 3 = 1)
    (hX1 : X ≠ 1) {B : SL(2, F)} (h : B * X * B⁻¹ = X ∨ B * X * B⁻¹ = -X) : B * X * B⁻¹ = X := by
  rcases h with h | h
  · exact h
  · exfalso
    have e := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F).trace) h
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.trace_neg] at e
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul,
      trace_eq_neg_one hX3 hX1] at e
    apply h2
    linear_combination -e

theorem eq_add_smul_of_commute {X W : Matrix (Fin 2) (Fin 2) F} (hX : ¬ IsScalar2 X)
    (hW : W * X = X * W) : ∃ a b : F, W = a • 1 + b • X := by
  obtain ⟨c1, c2, c3⟩ := Item228Census3Proof.commute_conditions hW
  by_cases h01 : X 0 1 = 0
  · by_cases h10 : X 1 0 = 0
    · have hd : X 0 0 - X 1 1 ≠ 0 := fun h => hX ⟨h01, h10, sub_eq_zero.mp h⟩
      have hw01 : W 0 1 = 0 := by
        have : W 0 1 * (X 0 0 - X 1 1) = 0 := by rw [← c2, h01, zero_mul]
        exact (mul_eq_zero.mp this).resolve_right hd
      have hw10 : W 1 0 = 0 := by
        have : W 1 0 * (X 0 0 - X 1 1) = 0 := by rw [c3, h10, zero_mul]
        exact (mul_eq_zero.mp this).resolve_right hd
      refine ⟨W 0 0 - (W 0 0 - W 1 1) / (X 0 0 - X 1 1) * X 0 0,
        (W 0 0 - W 1 1) / (X 0 0 - X 1 1), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h10, hw01, hw10]
      field_simp
      ring1
    · have hw01 : W 0 1 = 0 := by
        have : W 0 1 * X 1 0 = 0 := by rw [c1, h01, zero_mul]
        exact (mul_eq_zero.mp this).resolve_right h10
      refine ⟨W 0 0 - W 1 0 / X 1 0 * X 0 0, W 1 0 / X 1 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, hw01] <;> field_simp
      first | ring1 | linear_combination c3
  · refine ⟨W 0 0 - W 0 1 / X 0 1 * X 0 0, W 0 1 / X 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp <;>
      first | ring1 | linear_combination c1 | linear_combination -c1 | linear_combination c2 |
        linear_combination -c2

theorem det_zMat {X : Matrix (Fin 2) (Fin 2) F} (hdet : X.det = 1) (htr : X.trace = -1)
    (c : F) : (c • ((2 : F) • X + 1)).det = 3 * c ^ 2 := by
  rw [Matrix.det_fin_two] at hdet ⊢
  rw [Matrix.trace_fin_two] at htr
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply_eq, smul_eq_mul,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  linear_combination (4 * c ^ 2) * hdet + (2 * c ^ 2) * htr

@[expose] noncomputable def zSL {c : F} (hc : 3 * c ^ 2 = 1) {X : SL(2, F)} (hX3 : X ^ 3 = 1)
    (hX1 : X ≠ 1) : SL(2, F) :=
  ⟨c • ((2 : F) • (X : Matrix (Fin 2) (Fin 2) F) + 1), by
    rw [det_zMat X.2 (trace_eq_neg_one hX3 hX1), hc]⟩

theorem coe_zSL {c : F} (hc : 3 * c ^ 2 = 1) {X : SL(2, F)} (hX3 : X ^ 3 = 1) (hX1 : X ≠ 1) :
    ((zSL hc hX3 hX1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      c • ((2 : F) • (X : Matrix (Fin 2) (Fin 2) F) + 1) :=
  rfl

theorem zSL_mul_comm {c : F} (hc : 3 * c ^ 2 = 1) {X : SL(2, F)} (hX3 : X ^ 3 = 1)
    (hX1 : X ≠ 1) : zSL hc hX3 hX1 * X = X * zSL hc hX3 hX1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_zSL]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem commute_zSL_of_commute {c : F} (hc : 3 * c ^ 2 = 1) {X : SL(2, F)} (hX3 : X ^ 3 = 1)
    (hX1 : X ≠ 1) {B : SL(2, F)} (h : B * X = X * B) :
    B * zSL hc hX3 hX1 = zSL hc hX3 hX1 * B := by
  apply Subtype.ext
  have hm : (B : Matrix (Fin 2) (Fin 2) F) * X = X * B := by
    have := congrArg Subtype.val h
    simpa using this
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_zSL,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, hm, Matrix.mul_one, Matrix.one_mul]

theorem zSL_mul_self {c : F} (hc : 3 * c ^ 2 = 1) {X : SL(2, F)} (hX3 : X ^ 3 = 1)
    (hX1 : X ≠ 1) : zSL hc hX3 hX1 * zSL hc hX3 hX1 = -1 := by
  apply Subtype.ext
  have hq := sq_add_self_add_one hX3 hX1
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_zSL, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  have e : (c • ((2 : F) • (X : Matrix (Fin 2) (Fin 2) F) + 1)) *
      (c • ((2 : F) • (X : Matrix (Fin 2) (Fin 2) F) + 1)) =
      (c * c) • ((4 : F) • ((X : Matrix (Fin 2) (Fin 2) F) * X + X + 1) -
        (3 : F) • (1 : Matrix (Fin 2) (Fin 2) F)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_add, smul_smul]
    module
  rw [e, hq, smul_zero, zero_sub, smul_neg, smul_smul]
  have : c * c * 3 = 1 := by linear_combination hc
  rw [this, one_smul]

theorem zSL_ne {c : F} (hc : 3 * c ^ 2 = 1) {X : SL(2, F)} (hX3 : X ^ 3 = 1) (hX1 : X ≠ 1)
    (h2 : (2 : F) ≠ 0) : zSL hc hX3 hX1 ≠ 1 ∧ zSL hc hX3 hX1 ≠ -1 := by
  have hne : (1 : SL(2, F)) ≠ -1 := by
    intro h
    have e := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp at e
    apply h2
    linear_combination e
  have hz := zSL_mul_self hc hX3 hX1
  constructor
  · intro h
    rw [h, one_mul] at hz
    exact hne hz
  · intro h
    rw [h] at hz
    apply hne
    rw [← hz]
    apply Subtype.ext
    simp

theorem eq_or_of_commute_of_sq (h3 : (3 : F) ≠ 0) {c : F} (hc : 3 * c ^ 2 = 1) {X : SL(2, F)}
    (hX3 : X ^ 3 = 1) (hX1 : X ≠ 1) {W : SL(2, F)} (hWX : W * X = X * W)
    (hW2 : W * W = 1 ∨ W * W = -1) :
    W = 1 ∨ W = -1 ∨ W = zSL hc hX3 hX1 ∨ W = -zSL hc hX3 hX1 := by
  have hns := not_isScalar2_of_cube h3 hX3 hX1
  have hq := sq_add_self_add_one hX3 hX1
  have hWXm : (W : Matrix (Fin 2) (Fin 2) F) * X = X * W := by
    have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) hWX
    simpa using this
  obtain ⟨a, b, hab⟩ := eq_add_smul_of_commute hns hWXm
  set Xm := (X : Matrix (Fin 2) (Fin 2) F) with hXm
  have hdetX := X.2
  have htr := trace_eq_neg_one hX3 hX1
  have hsq : (W : Matrix (Fin 2) (Fin 2) F) * W =
      (a * a - b * b) • (1 : Matrix (Fin 2) (Fin 2) F) + (2 * a * b - b * b) • Xm := by
    rw [hab]
    have hXX : Xm * Xm = -Xm - 1 := by
      rw [← sub_eq_zero]
      rw [show Xm * Xm - (-Xm - 1) = Xm * Xm + Xm + 1 by abel]
      exact hq
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hXX]
    module
  have hdetW : a * a - a * b + b * b = 1 := by
    have h1 := W.2
    rw [hab, Matrix.det_fin_two] at h1
    rw [Matrix.det_fin_two] at hdetX
    rw [Matrix.trace_fin_two] at htr
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h1
    linear_combination h1 - b * b * hdetX - a * b * htr
  have hcoef : 2 * a * b - b * b = 0 := by
    by_contra hne
    apply hns
    have hW2m : (W : Matrix (Fin 2) (Fin 2) F) * W = 1 ∨
        (W : Matrix (Fin 2) (Fin 2) F) * W = -1 := by
      rcases hW2 with h | h
      · left
        have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) h
        simpa using this
      · right
        have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) h
        simpa [Matrix.SpecialLinearGroup.coe_neg] using this
    obtain ⟨e, he⟩ : ∃ e : F, (W : Matrix (Fin 2) (Fin 2) F) * W = e • 1 := by
      rcases hW2m with h | h
      · exact ⟨1, by rw [h, one_smul]⟩
      · exact ⟨-1, by rw [h, neg_one_smul]⟩
    have hXs : Xm = ((2 * a * b - b * b)⁻¹ * (e - (a * a - b * b))) • 1 := by
      have h0 := hsq.symm.trans he
      have h1 : (2 * a * b - b * b) • Xm = (e - (a * a - b * b)) • (1 : Matrix (Fin 2) (Fin 2) F) :=
        by
        calc (2 * a * b - b * b) • Xm = e • 1 - (a * a - b * b) • 1 := by rw [← h0]; abel
          _ = (e - (a * a - b * b)) • (1 : Matrix (Fin 2) (Fin 2) F) := (sub_smul _ _ _).symm
      rw [← smul_smul, ← h1, smul_smul, inv_mul_cancel₀ hne, one_smul]
    refine ⟨?_, ?_, ?_⟩ <;> rw [hXs] <;> simp
  rcases eq_or_ne b 0 with hb | hb
  ·
    rw [hb, mul_zero, sub_zero, mul_zero, add_zero] at hdetW
    rcases mul_self_eq_one_iff.mp hdetW with ha | ha
    · left
      apply Subtype.ext
      rw [hab, ha, hb, zero_smul, add_zero, one_smul, Matrix.SpecialLinearGroup.coe_one]
    · right; left
      apply Subtype.ext
      rw [hab, ha, hb, zero_smul, add_zero, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one, neg_one_smul]
  ·
    have hb2 : b = 2 * a := by
      have : b * (2 * a - b) = 0 := by linear_combination hcoef
      exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hb)).symm
    have ha2 : a * a = c * c := by
      rw [hb2] at hdetW
      have h0 : 3 * (a * a - c * c) = 0 := by linear_combination hdetW - hc
      have h1 := (mul_eq_zero.mp h0).resolve_left h3
      linear_combination h1
    have hW : (W : Matrix (Fin 2) (Fin 2) F) = a • ((2 : F) • Xm + 1) := by
      rw [hab, hb2, smul_add, smul_smul, mul_comm a 2, add_comm]
    rcases mul_self_eq_mul_self_iff.mp ha2 with ha | ha
    · right; right; left
      apply Subtype.ext
      rw [hW, coe_zSL, ha]
    · right; right; right
      apply Subtype.ext
      rw [hW, Matrix.SpecialLinearGroup.coe_neg, coe_zSL, ha, neg_smul]

theorem conj_eq_of_conj_zSL (h2 : (2 : F) ≠ 0) {c : F} (hc : 3 * c ^ 2 = 1) {X : SL(2, F)}
    (hX3 : X ^ 3 = 1) (hX1 : X ≠ 1) {B : SL(2, F)}
    (h : B * zSL hc hX3 hX1 * B⁻¹ = zSL hc hX3 hX1 ∨ B * zSL hc hX3 hX1 * B⁻¹ = -zSL hc hX3 hX1) :
    B * X * B⁻¹ = X ∨ B * X * B⁻¹ = X⁻¹ := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc
  have hBB' : (B : Matrix (Fin 2) (Fin 2) F) *
      ((B⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hconj : ((B * zSL hc hX3 hX1 * B⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      c • ((2 : F) • ((B * X * B⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) + 1) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_zSL]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hBB']
  have hinj : Function.Injective (fun A : Matrix (Fin 2) (Fin 2) F => c • A) :=
    smul_right_injective _ hc0
  have hinj2 : Function.Injective (fun A : Matrix (Fin 2) (Fin 2) F => (2 : F) • A) :=
    smul_right_injective _ h2
  have hq := sq_add_self_add_one hX3 hX1
  rcases h with h | h
  · left
    apply Subtype.ext
    have e : ((B * zSL hc hX3 hX1 * B⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        ((zSL hc hX3 hX1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := congrArg Subtype.val h
    rw [hconj, coe_zSL] at e
    exact hinj2 (add_right_cancel (hinj e))
  · right
    apply Subtype.ext
    have e : ((B * zSL hc hX3 hX1 * B⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        ((-zSL hc hX3 hX1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := congrArg Subtype.val h
    rw [hconj, Matrix.SpecialLinearGroup.coe_neg, coe_zSL, ← smul_neg] at e
    have e1 := hinj e
    have e2 : (2 : F) • ((B * X * B⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        (2 : F) • (-(X : Matrix (Fin 2) (Fin 2) F) - 1) := by
      rw [eq_sub_of_add_eq e1, smul_sub, smul_neg, two_smul F (1 : Matrix (Fin 2) (Fin 2) F)]
      abel
    have hY' := hinj2 e2
    rw [hY']
    have hXi : ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        (X : Matrix (Fin 2) (Fin 2) F) * X := by
      have h3 := mat_cube_eq_one hX3
      have hXX : ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * X = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
      calc ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
          ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
            ((X : Matrix (Fin 2) (Fin 2) F) * X * X) := by
            rw [h3, Matrix.mul_one]
        _ = (((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * X) * (X * X) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hXX, Matrix.one_mul]
    rw [hXi]
    rw [← sub_eq_zero]
    rw [show -(X : Matrix (Fin 2) (Fin 2) F) - 1 - (X : Matrix (Fin 2) (Fin 2) F) * X =
      -((X : Matrix (Fin 2) (Fin 2) F) * X + X + 1) by abel, hq, neg_zero]

end Item211Res4Proof

end CFSG.RankThree.PartTwo.Sec21
