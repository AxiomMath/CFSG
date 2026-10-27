module

public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnBits
public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnMat

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.TLn

open Matrix Hering214

@[expose] def colsOf5 (f : Fin 5 → Fin 5 → ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of fun i j => f j i

instance bdDec5 (X : List ℕ) : Decidable (Bd 5 X) := by unfold Bd; infer_instance

@[expose] def AB5 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1]

theorem A5_mul_B5 : A5 * B5 = AB5 := by decide

@[expose] def bits5 : List Bool :=
  [false, false, false, false, true, true, true, true, false, true,
   false, false, false, false, false, false, false, false, false, false]

theorem bsVal_bits5 : bsVal 1 bits5 = 1111040 := by decide

theorem vecP_5a : ∀ c : Fin 5 → ZMod 2, (A5 * A5 + A5 + 1) *ᵥ c = 0 →
    c 2 = 0 ∧ c 3 = 0 ∧ c 4 = 0 := by
  decide +kernel

theorem vecL_5a : ∀ c : Fin 5 → ZMod 2, (A5 + 1) *ᵥ c = 0 → c 0 = 0 ∧ c 1 = 0 := by
  decide +kernel

theorem vecP_5ab : ∀ c : Fin 5 → ZMod 2, (AB5 * AB5 + AB5 + 1) *ᵥ c = 0 → c 4 = 0 := by
  decide +kernel

theorem vecL_5ab : ∀ c : Fin 5 → ZMod 2, (AB5 + 1) *ᵥ c = 0 →
    c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 0 := by
  decide +kernel

@[expose] def code5a (x0 x1 y2 y3 y4 z2 z3 z4 v2 v3 v4 : ZMod 2) : List ℕ :=
  [x0.val + 2 * x1.val,
   x1.val + 2 * (x0+x1 : ZMod 2).val,
   4 * y2.val + 8 * z2.val + 16 * v2.val,
   4 * y3.val + 8 * z3.val + 16 * v3.val,
   4 * y4.val + 8 * z4.val + 16 * v4.val]

@[expose] def W5a : List (List ℕ × List ℕ) :=
  [([1, 2, 24, 8, 4], [1, 2, 16, 8, 12]),
   ([1, 2, 12, 8, 24], [1, 2, 12, 8, 24]),
   ([1, 2, 12, 20, 4], [1, 2, 16, 20, 24]),
   ([1, 2, 24, 8, 12], [1, 2, 24, 8, 12]),
   ([1, 2, 20, 8, 4], [1, 2, 16, 8, 20]),
   ([1, 2, 16, 12, 4], [1, 2, 16, 24, 4])]

theorem bd_5a : ∀ x0 x1 y2 y3 y4 z2 z3 z4 v2 v3 v4 : ZMod 2,
    Bd 5 (code5a x0 x1 y2 y3 y4 z2 z3 z4 v2 v3 v4) := by
  decide +kernel

theorem chk_5a : ∀ x0 x1 y2 y3 y4 z2 z3 z4 v2 v3 v4 : ZMod 2,
    chk 5 bits5 W5a (code5a x0 x1 y2 y3 y4 z2 z3 z4 v2 v3 v4) = true := by
  decide +kernel

theorem W_ok_5a : ∀ p ∈ W5a, Bd 5 p.1 ∧ Bd 5 p.2 ∧ toM 5 p.1 * toM 5 p.2 = 1 ∧
    toM 5 p.1 * A5 = A5 * toM 5 p.1 := by
  decide +kernel

theorem toM_code_5a : ∀ x0 x1 y2 y3 y4 z2 z3 z4 v2 v3 v4 : ZMod 2,
    toM 5 (code5a x0 x1 y2 y3 y4 z2 z3 z4 v2 v3 v4) =
      colsOf5 ![![x0, x1, 0, 0, 0],
        A5 *ᵥ ![x0, x1, 0, 0, 0],
        ![0, 0, y2, y3, y4],
        ![0, 0, z2, z3, z4],
        ![0, 0, v2, v3, v4]] := by
  decide +kernel

theorem eqCols_5a {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hA : M * A5 = A5 * M) :
    M = colsOf5 ![(fun k => M k 0),
        A5 *ᵥ (fun k => M k 0),
        (fun k => M k 2),
        (fun k => M k 3),
        (fun k => M k 4)] := by
  ext i j
  simp only [colsOf5, of_apply]
  fin_cases j
  · rfl
  · fin_cases i
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five, A5]
        using congrFun (congrFun hA 0) 0
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five, A5]
        using congrFun (congrFun hA 1) 0
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five, A5]
        using congrFun (congrFun hA 2) 0
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five, A5]
        using congrFun (congrFun hA 3) 0
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five, A5]
        using congrFun (congrFun hA 4) 0
  · rfl
  · rfl
  · rfl

theorem coords_5a {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hA : M * A5 = A5 * M) :
    ∃ x0 x1 y2 y3 y4 z2 z3 z4 v2 v3 v4 : ZMod 2,
      M = toM 5 (code5a x0 x1 y2 y3 y4 z2 z3 z4 v2 v3 v4) := by
  have h := eqCols_5a hA
  have e0 : (A5 * A5 + A5 + 1) *ᵥ (M *ᵥ Pi.single 0 1) = 0 :=
    vec_of_comm (comm_poly hA) _ (by decide)
  rw [← col_eq_mulVec] at e0
  obtain ⟨c0_2, c0_3, c0_4⟩ := vecP_5a _ e0
  have h0 : (fun k => M k 0) = ![M 0 0, M 1 0, 0, 0, 0] := by
    funext k; fin_cases k
    · rfl
    · rfl
    · exact c0_2
    · exact c0_3
    · exact c0_4
  have e2 : (A5 + 1) *ᵥ (M *ᵥ Pi.single 2 1) = 0 :=
    vec_of_comm (comm_lin hA) _ (by decide)
  rw [← col_eq_mulVec] at e2
  obtain ⟨c2_0, c2_1⟩ := vecL_5a _ e2
  have h2 : (fun k => M k 2) = ![0, 0, M 2 2, M 3 2, M 4 2] := by
    funext k; fin_cases k
    · exact c2_0
    · exact c2_1
    · rfl
    · rfl
    · rfl
  have e3 : (A5 + 1) *ᵥ (M *ᵥ Pi.single 3 1) = 0 :=
    vec_of_comm (comm_lin hA) _ (by decide)
  rw [← col_eq_mulVec] at e3
  obtain ⟨c3_0, c3_1⟩ := vecL_5a _ e3
  have h3 : (fun k => M k 3) = ![0, 0, M 2 3, M 3 3, M 4 3] := by
    funext k; fin_cases k
    · exact c3_0
    · exact c3_1
    · rfl
    · rfl
    · rfl
  have e4 : (A5 + 1) *ᵥ (M *ᵥ Pi.single 4 1) = 0 :=
    vec_of_comm (comm_lin hA) _ (by decide)
  rw [← col_eq_mulVec] at e4
  obtain ⟨c4_0, c4_1⟩ := vecL_5a _ e4
  have h4 : (fun k => M k 4) = ![0, 0, M 2 4, M 3 4, M 4 4] := by
    funext k; fin_cases k
    · exact c4_0
    · exact c4_1
    · rfl
    · rfl
    · rfl
  rw [h0, h2, h3, h4] at h
  refine ⟨M 0 0, M 1 0, M 2 2, M 3 2, M 4 2, M 2 3, M 3 3, M 4 3, M 2 4, M 3 4, M 4 4, ?_⟩
  rw [toM_code_5a]
  exact h

theorem hcode_5a {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hA : M * A5 = A5 * M) :
    ∃ X, Bd 5 X ∧ toM 5 X = M ∧ chk 5 bits5 W5a X = true := by
  obtain ⟨x0, x1, y2, y3, y4, z2, z3, z4, v2, v3, v4, h⟩ := coords_5a hA
  exact ⟨code5a x0 x1 y2 y3 y4 z2 z3 z4 v2 v3 v4, bd_5a x0 x1 y2 y3 y4 z2 z3 z4 v2 v3 v4, h.symm,
    chk_5a x0 x1 y2 y3 y4 z2 z3 z4 v2 v3 v4⟩

@[expose] def code5ab (x0 x1 x2 x3 y0 y1 y2 y3 v4 : ZMod 2) : List ℕ :=
  [x0.val + 2 * x1.val + 4 * y0.val + 8 * y1.val,
   x1.val + 2 * (x0+x1 : ZMod 2).val + 4 * y1.val + 8 * (y0+y1 : ZMod 2).val,
   x2.val + 2 * x3.val + 4 * y2.val + 8 * y3.val,
   x3.val + 2 * (x2+x3 : ZMod 2).val + 4 * y3.val + 8 * (y2+y3 : ZMod 2).val,
   16 * v4.val]

@[expose] def W5ab : List (List ℕ × List ℕ) :=
  [([5, 10, 1, 2, 16], [4, 8, 5, 10, 16]),
   ([11, 13, 1, 2, 16], [4, 8, 11, 13, 16]),
   ([14, 7, 1, 2, 16], [4, 8, 14, 7, 16]),
   ([6, 11, 1, 2, 16], [4, 8, 9, 14, 16]),
   ([7, 9, 1, 2, 16], [4, 8, 13, 6, 16])]

theorem bd_5ab : ∀ x0 x1 x2 x3 y0 y1 y2 y3 v4 : ZMod 2,
    Bd 5 (code5ab x0 x1 x2 x3 y0 y1 y2 y3 v4) := by
  decide +kernel

theorem chk_5ab : ∀ x0 x1 x2 x3 y0 y1 y2 y3 v4 : ZMod 2,
    chk 5 bits5 W5ab (code5ab x0 x1 x2 x3 y0 y1 y2 y3 v4) = true := by
  decide +kernel

theorem W_ok_5ab : ∀ p ∈ W5ab, Bd 5 p.1 ∧ Bd 5 p.2 ∧ toM 5 p.1 * toM 5 p.2 = 1 ∧
    toM 5 p.1 * AB5 = AB5 * toM 5 p.1 := by
  decide +kernel

theorem toM_code_5ab : ∀ x0 x1 x2 x3 y0 y1 y2 y3 v4 : ZMod 2,
    toM 5 (code5ab x0 x1 x2 x3 y0 y1 y2 y3 v4) =
      colsOf5 ![![x0, x1, x2, x3, 0],
        AB5 *ᵥ ![x0, x1, x2, x3, 0],
        ![y0, y1, y2, y3, 0],
        AB5 *ᵥ ![y0, y1, y2, y3, 0],
        ![0, 0, 0, 0, v4]] := by
  decide +kernel

theorem eqCols_5ab {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hA : M * AB5 = AB5 * M) :
    M = colsOf5 ![(fun k => M k 0),
        AB5 *ᵥ (fun k => M k 0),
        (fun k => M k 2),
        AB5 *ᵥ (fun k => M k 2),
        (fun k => M k 4)] := by
  ext i j
  simp only [colsOf5, of_apply]
  fin_cases j
  · rfl
  · fin_cases i
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five, AB5]
        using congrFun (congrFun hA 0) 0
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five, AB5]
        using congrFun (congrFun hA 1) 0
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five, AB5]
        using congrFun (congrFun hA 2) 0
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five, AB5]
        using congrFun (congrFun hA 3) 0
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five, AB5]
        using congrFun (congrFun hA 4) 0
  · rfl
  · fin_cases i
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five, AB5]
        using congrFun (congrFun hA 0) 2
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five, AB5]
        using congrFun (congrFun hA 1) 2
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five, AB5]
        using congrFun (congrFun hA 2) 2
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five, AB5]
        using congrFun (congrFun hA 3) 2
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five, AB5]
        using congrFun (congrFun hA 4) 2
  · rfl

theorem coords_5ab {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hA : M * AB5 = AB5 * M) :
    ∃ x0 x1 x2 x3 y0 y1 y2 y3 v4 : ZMod 2,
      M = toM 5 (code5ab x0 x1 x2 x3 y0 y1 y2 y3 v4) := by
  have h := eqCols_5ab hA
  have e0 : (AB5 * AB5 + AB5 + 1) *ᵥ (M *ᵥ Pi.single 0 1) = 0 :=
    vec_of_comm (comm_poly hA) _ (by decide)
  rw [← col_eq_mulVec] at e0
  obtain c0_4 := (vecP_5ab _ e0)
  have h0 : (fun k => M k 0) = ![M 0 0, M 1 0, M 2 0, M 3 0, 0] := by
    funext k; fin_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact c0_4
  have e2 : (AB5 * AB5 + AB5 + 1) *ᵥ (M *ᵥ Pi.single 2 1) = 0 :=
    vec_of_comm (comm_poly hA) _ (by decide)
  rw [← col_eq_mulVec] at e2
  obtain c2_4 := (vecP_5ab _ e2)
  have h2 : (fun k => M k 2) = ![M 0 2, M 1 2, M 2 2, M 3 2, 0] := by
    funext k; fin_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact c2_4
  have e4 : (AB5 + 1) *ᵥ (M *ᵥ Pi.single 4 1) = 0 :=
    vec_of_comm (comm_lin hA) _ (by decide)
  rw [← col_eq_mulVec] at e4
  obtain ⟨c4_0, c4_1, c4_2, c4_3⟩ := vecL_5ab _ e4
  have h4 : (fun k => M k 4) = ![0, 0, 0, 0, M 4 4] := by
    funext k; fin_cases k
    · exact c4_0
    · exact c4_1
    · exact c4_2
    · exact c4_3
    · rfl
  rw [h0, h2, h4] at h
  refine ⟨M 0 0, M 1 0, M 2 0, M 3 0, M 0 2, M 1 2, M 2 2, M 3 2, M 4 4, ?_⟩
  rw [toM_code_5ab]
  exact h

theorem hcode_5ab {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hA : M * AB5 = AB5 * M) :
    ∃ X, Bd 5 X ∧ toM 5 X = M ∧ chk 5 bits5 W5ab X = true := by
  obtain ⟨x0, x1, x2, x3, y0, y1, y2, y3, v4, h⟩ := coords_5ab hA
  exact ⟨code5ab x0 x1 x2 x3 y0 y1 y2 y3 v4, bd_5ab x0 x1 x2 x3 y0 y1 y2 y3 v4, h.symm,
    chk_5ab x0 x1 x2 x3 y0 y1 y2 y3 v4⟩

end CFSG.RankThree.PartTwo.Sec21.FF79.TLn
