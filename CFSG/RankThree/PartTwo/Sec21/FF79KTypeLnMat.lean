module

public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnGen

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.TLn

open Matrix Hering214

@[expose] def R1M4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
@[expose] def R2M4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
@[expose] def WM4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

@[expose] def sR1_4 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨R1M4, det_eq_one_of_mul_eq_one_two R1M4 R1M4 (by decide)⟩
@[expose] def sR2_4 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨R2M4, det_eq_one_of_mul_eq_one_two R2M4 R2M4 (by decide)⟩
@[expose] def sW4 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨WM4, det_eq_one_of_mul_eq_one_two WM4 WM4 (by decide)⟩

theorem normData4 : NormData sA4 sB4 sR1_4 sR2_4 sW4 :=
  ⟨⟨by decide, by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

theorem sym4 : ∀ i j : Fin 3, ((sA4 ^ (i : ℕ) * sB4 ^ (j : ℕ) : SpecialLinearGroup (Fin 4)
    (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ =
    ((sA4 ^ (i : ℕ) * sB4 ^ (j : ℕ) : SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) := by decide

theorem trace4 : ∀ i j : Fin 3,
    ((sA4 ^ (i : ℕ) * sB4 ^ (j : ℕ) : SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)).trace = (sA4 : Matrix (Fin 4) (Fin 4) (ZMod 2)).trace →
    ((i = 1 ∨ i = 2) ∧ j = 0) ∨ (i = 0 ∧ (j = 1 ∨ j = 2)) := by decide

theorem trace4' : (sB4 : Matrix (Fin 4) (Fin 4) (ZMod 2)).trace =
    (sA4 : Matrix (Fin 4) (Fin 4) (ZMod 2)).trace := by decide


@[expose] def R1M5 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
@[expose] def R2M5 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1]
@[expose] def WM5 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1]

@[expose] def sR1_5 : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨R1M5, det_eq_one_of_mul_eq_one_two R1M5 R1M5 (by decide)⟩
@[expose] def sR2_5 : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨R2M5, det_eq_one_of_mul_eq_one_two R2M5 R2M5 (by decide)⟩
@[expose] def sW5 : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨WM5, det_eq_one_of_mul_eq_one_two WM5 WM5 (by decide)⟩

theorem normData5 : NormData sA5 sB5 sR1_5 sR2_5 sW5 :=
  ⟨⟨by decide, by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

theorem sym5 : ∀ i j : Fin 3, ((sA5 ^ (i : ℕ) * sB5 ^ (j : ℕ) : SpecialLinearGroup (Fin 5)
    (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ =
    ((sA5 ^ (i : ℕ) * sB5 ^ (j : ℕ) : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) := by decide

theorem trace5 : ∀ i j : Fin 3,
    ((sA5 ^ (i : ℕ) * sB5 ^ (j : ℕ) : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)).trace = (sA5 : Matrix (Fin 5) (Fin 5) (ZMod 2)).trace →
    ((i = 1 ∨ i = 2) ∧ j = 0) ∨ (i = 0 ∧ (j = 1 ∨ j = 2)) := by decide

theorem trace5' : (sB5 : Matrix (Fin 5) (Fin 5) (ZMod 2)).trace =
    (sA5 : Matrix (Fin 5) (Fin 5) (ZMod 2)).trace := by decide

def col4 (c0 c2 : Fin 4 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun i j => ![c0 i, (A4 *ᵥ c0) i, c2 i, (B4 *ᵥ c2) i] j

theorem cent4_dec : ∀ c0 c2 : Fin 4 → ZMod 2,
    col4 c0 c2 * A4 = A4 * col4 c0 c2 → col4 c0 c2 * B4 = B4 * col4 c0 c2 →
    (∀ v : Fin 4 → ZMod 2, col4 c0 c2 *ᵥ v = 0 → v = 0) →
    ∃ i j : Fin 3, col4 c0 c2 = A4 ^ (i : ℕ) * B4 ^ (j : ℕ) := by
  decide +kernel

theorem eq_col4 {s : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hA : s * A4 = A4 * s)
    (hB : s * B4 = B4 * s) : s = col4 (fun k => s k 0) (fun k => s k 2) := by
  ext i j
  have h1 := congrFun (congrFun hA i) 0
  have h3 := congrFun (congrFun hB i) 2
  simp only [col4, of_apply]
  fin_cases j
  · rfl
  · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, A4] using h1
  · rfl
  · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, B4] using h3

def col5 (c0 c2 c4 : Fin 5 → ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of fun i j => ![c0 i, (A5 *ᵥ c0) i, c2 i, (B5 *ᵥ c2) i, c4 i] j

theorem eq_col5 {s : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hA : s * A5 = A5 * s)
    (hB : s * B5 = B5 * s) : s = col5 (fun k => s k 0) (fun k => s k 2) (fun k => s k 4) := by
  ext i j
  have h1 := congrFun (congrFun hA i) 0
  have h3 := congrFun (congrFun hB i) 2
  simp only [col5, of_apply]
  fin_cases j
  · rfl
  · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five, A5] using h1
  · rfl
  · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five, B5] using h3
  · rfl

theorem vec_of_comm {n : ℕ} {s X : Matrix (Fin n) (Fin n) (ZMod 2)} (h : s * X = X * s)
    (v : Fin n → ZMod 2) (hv : X *ᵥ v = 0) : X *ᵥ (s *ᵥ v) = 0 := by
  rw [Matrix.mulVec_mulVec, ← h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

theorem comm_poly {n : ℕ} {s X : Matrix (Fin n) (Fin n) (ZMod 2)} (h : s * X = X * s) :
    s * (X * X + X + 1) = (X * X + X + 1) * s := by
  simp only [mul_add, add_mul, mul_one, one_mul, ← mul_assoc, h]
  rw [mul_assoc, h, ← mul_assoc]

theorem comm_lin {n : ℕ} {s X : Matrix (Fin n) (Fin n) (ZMod 2)} (h : s * X = X * s) :
    s * (X + 1) = (X + 1) * s := by
  rw [mul_add, add_mul, h, mul_one, one_mul]

theorem vec0_5 : ∀ c0 : Fin 5 → ZMod 2, (A5 * A5 + A5 + 1) *ᵥ c0 = 0 → (B5 + 1) *ᵥ c0 = 0 →
    c0 2 = 0 ∧ c0 3 = 0 ∧ c0 4 = 0 := by decide +kernel

theorem vec2_5 : ∀ c2 : Fin 5 → ZMod 2, (B5 * B5 + B5 + 1) *ᵥ c2 = 0 → (A5 + 1) *ᵥ c2 = 0 →
    c2 0 = 0 ∧ c2 1 = 0 ∧ c2 4 = 0 := by decide +kernel

theorem vec4_5 : ∀ c4 : Fin 5 → ZMod 2, (A5 + 1) *ᵥ c4 = 0 → (B5 + 1) *ᵥ c4 = 0 →
    c4 0 = 0 ∧ c4 1 = 0 ∧ c4 2 = 0 ∧ c4 3 = 0 := by decide +kernel

theorem cent5_dec : ∀ x0 x1 y2 y3 z4 : ZMod 2,
    col5 ![x0, x1, 0, 0, 0] ![0, 0, y2, y3, 0] ![0, 0, 0, 0, z4] * A5 =
      A5 * col5 ![x0, x1, 0, 0, 0] ![0, 0, y2, y3, 0] ![0, 0, 0, 0, z4] →
    col5 ![x0, x1, 0, 0, 0] ![0, 0, y2, y3, 0] ![0, 0, 0, 0, z4] * B5 =
      B5 * col5 ![x0, x1, 0, 0, 0] ![0, 0, y2, y3, 0] ![0, 0, 0, 0, z4] →
    (∀ v : Fin 5 → ZMod 2,
      col5 ![x0, x1, 0, 0, 0] ![0, 0, y2, y3, 0] ![0, 0, 0, 0, z4] *ᵥ v = 0 → v = 0) →
    ∃ i j : Fin 3, col5 ![x0, x1, 0, 0, 0] ![0, 0, y2, y3, 0] ![0, 0, 0, 0, z4] =
      A5 ^ (i : ℕ) * B5 ^ (j : ℕ) := by
  decide +kernel


theorem sl_mulVec_eq_zero {n : ℕ} (g : SpecialLinearGroup (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) (h : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = 0) : v = 0 := by
  have h1 : (g : Matrix (Fin n) (Fin n) (ZMod 2)).adjugate *
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [Matrix.adjugate_mul, g.2, one_smul]
  calc v = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v := (Matrix.one_mulVec v).symm
    _ = 0 := by rw [← h1, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

theorem sl_comm_coe {n : ℕ} {g h : SpecialLinearGroup (Fin n) (ZMod 2)} (e : g * h = h * g) :
    (g : Matrix (Fin n) (Fin n) (ZMod 2)) * h = h * g := by
  have := congrArg (fun x : SpecialLinearGroup (Fin n) (ZMod 2) =>
    (x : Matrix (Fin n) (Fin n) (ZMod 2))) e
  simpa using this

theorem col_eq_mulVec {n : ℕ} (s : Matrix (Fin n) (Fin n) (ZMod 2)) (j : Fin n) :
    (fun k => s k j) = s *ᵥ Pi.single j 1 := by
  funext k
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem coe_sA4 : (sA4 : Matrix (Fin 4) (Fin 4) (ZMod 2)) = A4 := rfl
theorem coe_sB4 : (sB4 : Matrix (Fin 4) (Fin 4) (ZMod 2)) = B4 := rfl
theorem coe_sA5 : (sA5 : Matrix (Fin 5) (Fin 5) (ZMod 2)) = A5 := rfl
theorem coe_sB5 : (sB5 : Matrix (Fin 5) (Fin 5) (ZMod 2)) = B5 := rfl

theorem cent4_mat (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hA : M * A4 = A4 * M)
    (hB : M * B4 = B4 * M) (hinv : ∀ v, M *ᵥ v = 0 → v = 0) :
    ∃ i j : Fin 3, M = A4 ^ (i : ℕ) * B4 ^ (j : ℕ) := by
  have h := eq_col4 hA hB
  obtain ⟨i, j, hij⟩ := cent4_dec (fun k => M k 0) (fun k => M k 2)
    (by rw [← h]; exact hA) (by rw [← h]; exact hB) (fun v hv => hinv v (by rw [h]; exact hv))
  exact ⟨i, j, h.trans hij⟩

theorem cent5_mat (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) (hA : M * A5 = A5 * M)
    (hB : M * B5 = B5 * M) (hinv : ∀ v, M *ᵥ v = 0 → v = 0) :
    ∃ i j : Fin 3, M = A5 ^ (i : ℕ) * B5 ^ (j : ℕ) := by
  have h := eq_col5 hA hB
  have e0 : (A5 * A5 + A5 + 1) *ᵥ (M *ᵥ Pi.single 0 1) = 0 :=
    vec_of_comm (comm_poly hA) _ (by decide)
  have e0' : (B5 + 1) *ᵥ (M *ᵥ Pi.single 0 1) = 0 := vec_of_comm (comm_lin hB) _ (by decide)
  have e2 : (B5 * B5 + B5 + 1) *ᵥ (M *ᵥ Pi.single 2 1) = 0 :=
    vec_of_comm (comm_poly hB) _ (by decide)
  have e2' : (A5 + 1) *ᵥ (M *ᵥ Pi.single 2 1) = 0 := vec_of_comm (comm_lin hA) _ (by decide)
  have e4 : (A5 + 1) *ᵥ (M *ᵥ Pi.single 4 1) = 0 := vec_of_comm (comm_lin hA) _ (by decide)
  have e4' : (B5 + 1) *ᵥ (M *ᵥ Pi.single 4 1) = 0 := vec_of_comm (comm_lin hB) _ (by decide)
  rw [← col_eq_mulVec] at e0 e0' e2 e2' e4 e4'
  obtain ⟨c02, c03, c04⟩ := vec0_5 _ e0 e0'
  obtain ⟨c20, c21, c24⟩ := vec2_5 _ e2 e2'
  obtain ⟨c40, c41, c42, c43⟩ := vec4_5 _ e4 e4'
  have h0 : (fun k => M k 0) = ![M 0 0, M 1 0, 0, 0, 0] := by
    funext k; fin_cases k
    · rfl
    · rfl
    · exact c02
    · exact c03
    · exact c04
  have h2 : (fun k => M k 2) = ![0, 0, M 2 2, M 3 2, 0] := by
    funext k; fin_cases k
    · exact c20
    · exact c21
    · rfl
    · rfl
    · exact c24
  have h4 : (fun k => M k 4) = ![0, 0, 0, 0, M 4 4] := by
    funext k; fin_cases k
    · exact c40
    · exact c41
    · exact c42
    · exact c43
    · rfl
  rw [h0, h2, h4] at h
  obtain ⟨i, j, hij⟩ := cent5_dec (M 0 0) (M 1 0) (M 2 2) (M 3 2) (M 4 4)
    (by rw [← h]; exact hA) (by rw [← h]; exact hB) (fun v hv => hinv v (by rw [h]; exact hv))
  exact ⟨i, j, h.trans hij⟩

theorem cent4_sl (s : SpecialLinearGroup (Fin 4) (ZMod 2)) (hA : s * sA4 = sA4 * s)
    (hB : s * sB4 = sB4 * s) : ∃ i j : Fin 3, s = sA4 ^ (i : ℕ) * sB4 ^ (j : ℕ) := by
  obtain ⟨i, j, h⟩ := cent4_mat s (by simpa [coe_sA4] using sl_comm_coe hA)
    (by simpa [coe_sB4] using sl_comm_coe hB) (sl_mulVec_eq_zero s)
  refine ⟨i, j, Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_⟩
  have := congrFun (congrFun h a) b
  simpa [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_pow, coe_sA4, coe_sB4] using this

theorem cent5_sl (s : SpecialLinearGroup (Fin 5) (ZMod 2)) (hA : s * sA5 = sA5 * s)
    (hB : s * sB5 = sB5 * s) : ∃ i j : Fin 3, s = sA5 ^ (i : ℕ) * sB5 ^ (j : ℕ) := by
  obtain ⟨i, j, h⟩ := cent5_mat s (by simpa [coe_sA5] using sl_comm_coe hA)
    (by simpa [coe_sB5] using sl_comm_coe hB) (sl_mulVec_eq_zero s)
  refine ⟨i, j, Matrix.SpecialLinearGroup.ext _ _ fun a b => ?_⟩
  have := congrFun (congrFun h a) b
  simpa [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_pow, coe_sA5, coe_sB5] using this

end CFSG.RankThree.PartTwo.Sec21.FF79.TLn
