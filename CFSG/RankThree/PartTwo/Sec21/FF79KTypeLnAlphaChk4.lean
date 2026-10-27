module

public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnBits
public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnMat

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.TLn

open Matrix Hering214

@[expose] def colsOf4 (f : Fin 4 → Fin 4 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun i j => f j i

instance bdDec4 (X : List ℕ) : Decidable (Bd 4 X) := by unfold Bd; infer_instance

@[expose] def AB4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]

theorem A4_mul_B4 : A4 * B4 = AB4 := by decide

@[expose] def bits4 : List Bool :=
  [false, false, false, true, true, false, false, false, false, false,
   false]

theorem bsVal_bits4 : bsVal 1 bits4 = 2240 := by decide

theorem vecP_4a : ∀ c : Fin 4 → ZMod 2, (A4 * A4 + A4 + 1) *ᵥ c = 0 → c 2 = 0 ∧ c 3 = 0 := by
  decide +kernel

theorem vecL_4a : ∀ c : Fin 4 → ZMod 2, (A4 + 1) *ᵥ c = 0 → c 0 = 0 ∧ c 1 = 0 := by
  decide +kernel

@[expose] def code4a (x0 x1 y2 y3 z2 z3 : ZMod 2) : List ℕ :=
  [x0.val + 2 * x1.val,
   x1.val + 2 * (x0+x1 : ZMod 2).val,
   4 * y2.val + 8 * z2.val,
   4 * y3.val + 8 * z3.val]

@[expose] def W4a : List (List ℕ × List ℕ) :=
  [([1, 2, 12, 4], [1, 2, 8, 12])]

theorem bd_4a : ∀ x0 x1 y2 y3 z2 z3 : ZMod 2,
    Bd 4 (code4a x0 x1 y2 y3 z2 z3) := by
  decide +kernel

theorem chk_4a : ∀ x0 x1 y2 y3 z2 z3 : ZMod 2,
    chk 4 bits4 W4a (code4a x0 x1 y2 y3 z2 z3) = true := by
  decide +kernel

theorem W_ok_4a : ∀ p ∈ W4a, Bd 4 p.1 ∧ Bd 4 p.2 ∧ toM 4 p.1 * toM 4 p.2 = 1 ∧
    toM 4 p.1 * A4 = A4 * toM 4 p.1 := by
  decide +kernel

theorem toM_code_4a : ∀ x0 x1 y2 y3 z2 z3 : ZMod 2,
    toM 4 (code4a x0 x1 y2 y3 z2 z3) =
      colsOf4 ![![x0, x1, 0, 0],
        A4 *ᵥ ![x0, x1, 0, 0],
        ![0, 0, y2, y3],
        ![0, 0, z2, z3]] := by
  decide +kernel

theorem eqCols_4a {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hA : M * A4 = A4 * M) :
    M = colsOf4 ![(fun k => M k 0),
        A4 *ᵥ (fun k => M k 0),
        (fun k => M k 2),
        (fun k => M k 3)] := by
  ext i j
  simp only [colsOf4, of_apply]
  fin_cases j
  · rfl
  · fin_cases i
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, A4]
        using congrFun (congrFun hA 0) 0
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, A4]
        using congrFun (congrFun hA 1) 0
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, A4]
        using congrFun (congrFun hA 2) 0
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, A4]
        using congrFun (congrFun hA 3) 0
  · rfl
  · rfl

theorem coords_4a {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hA : M * A4 = A4 * M) :
    ∃ x0 x1 y2 y3 z2 z3 : ZMod 2,
      M = toM 4 (code4a x0 x1 y2 y3 z2 z3) := by
  have h := eqCols_4a hA
  have e0 : (A4 * A4 + A4 + 1) *ᵥ (M *ᵥ Pi.single 0 1) = 0 :=
    vec_of_comm (comm_poly hA) _ (by decide)
  rw [← col_eq_mulVec] at e0
  obtain ⟨c0_2, c0_3⟩ := vecP_4a _ e0
  have h0 : (fun k => M k 0) = ![M 0 0, M 1 0, 0, 0] := by
    funext k; fin_cases k
    · rfl
    · rfl
    · exact c0_2
    · exact c0_3
  have e2 : (A4 + 1) *ᵥ (M *ᵥ Pi.single 2 1) = 0 :=
    vec_of_comm (comm_lin hA) _ (by decide)
  rw [← col_eq_mulVec] at e2
  obtain ⟨c2_0, c2_1⟩ := vecL_4a _ e2
  have h2 : (fun k => M k 2) = ![0, 0, M 2 2, M 3 2] := by
    funext k; fin_cases k
    · exact c2_0
    · exact c2_1
    · rfl
    · rfl
  have e3 : (A4 + 1) *ᵥ (M *ᵥ Pi.single 3 1) = 0 :=
    vec_of_comm (comm_lin hA) _ (by decide)
  rw [← col_eq_mulVec] at e3
  obtain ⟨c3_0, c3_1⟩ := vecL_4a _ e3
  have h3 : (fun k => M k 3) = ![0, 0, M 2 3, M 3 3] := by
    funext k; fin_cases k
    · exact c3_0
    · exact c3_1
    · rfl
    · rfl
  rw [h0, h2, h3] at h
  refine ⟨M 0 0, M 1 0, M 2 2, M 3 2, M 2 3, M 3 3, ?_⟩
  rw [toM_code_4a]
  exact h

theorem hcode_4a {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hA : M * A4 = A4 * M) :
    ∃ X, Bd 4 X ∧ toM 4 X = M ∧ chk 4 bits4 W4a X = true := by
  obtain ⟨x0, x1, y2, y3, z2, z3, h⟩ := coords_4a hA
  exact ⟨code4a x0 x1 y2 y3 z2 z3, bd_4a x0 x1 y2 y3 z2 z3, h.symm,
    chk_4a x0 x1 y2 y3 z2 z3⟩

@[expose] def code4ab (x0 x1 x2 x3 y0 y1 y2 y3 : ZMod 2) : List ℕ :=
  [x0.val + 2 * x1.val + 4 * y0.val + 8 * y1.val,
   x1.val + 2 * (x0+x1 : ZMod 2).val + 4 * y1.val + 8 * (y0+y1 : ZMod 2).val,
   x2.val + 2 * x3.val + 4 * y2.val + 8 * y3.val,
   x3.val + 2 * (x2+x3 : ZMod 2).val + 4 * y3.val + 8 * (y2+y3 : ZMod 2).val]

@[expose] def W4ab : List (List ℕ × List ℕ) :=
  [([5, 10, 1, 2], [4, 8, 5, 10]),
   ([11, 13, 1, 2], [4, 8, 11, 13]),
   ([14, 7, 1, 2], [4, 8, 14, 7]),
   ([6, 11, 1, 2], [4, 8, 9, 14]),
   ([7, 9, 1, 2], [4, 8, 13, 6])]

theorem bd_4ab : ∀ x0 x1 x2 x3 y0 y1 y2 y3 : ZMod 2,
    Bd 4 (code4ab x0 x1 x2 x3 y0 y1 y2 y3) := by
  decide +kernel

theorem chk_4ab : ∀ x0 x1 x2 x3 y0 y1 y2 y3 : ZMod 2,
    chk 4 bits4 W4ab (code4ab x0 x1 x2 x3 y0 y1 y2 y3) = true := by
  decide +kernel

theorem W_ok_4ab : ∀ p ∈ W4ab, Bd 4 p.1 ∧ Bd 4 p.2 ∧ toM 4 p.1 * toM 4 p.2 = 1 ∧
    toM 4 p.1 * AB4 = AB4 * toM 4 p.1 := by
  decide +kernel

theorem toM_code_4ab : ∀ x0 x1 x2 x3 y0 y1 y2 y3 : ZMod 2,
    toM 4 (code4ab x0 x1 x2 x3 y0 y1 y2 y3) =
      colsOf4 ![![x0, x1, x2, x3],
        AB4 *ᵥ ![x0, x1, x2, x3],
        ![y0, y1, y2, y3],
        AB4 *ᵥ ![y0, y1, y2, y3]] := by
  decide +kernel

theorem eqCols_4ab {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hA : M * AB4 = AB4 * M) :
    M = colsOf4 ![(fun k => M k 0),
        AB4 *ᵥ (fun k => M k 0),
        (fun k => M k 2),
        AB4 *ᵥ (fun k => M k 2)] := by
  ext i j
  simp only [colsOf4, of_apply]
  fin_cases j
  · rfl
  · fin_cases i
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, AB4]
        using congrFun (congrFun hA 0) 0
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, AB4]
        using congrFun (congrFun hA 1) 0
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, AB4]
        using congrFun (congrFun hA 2) 0
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, AB4]
        using congrFun (congrFun hA 3) 0
  · rfl
  · fin_cases i
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, AB4]
        using congrFun (congrFun hA 0) 2
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, AB4]
        using congrFun (congrFun hA 1) 2
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, AB4]
        using congrFun (congrFun hA 2) 2
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, AB4]
        using congrFun (congrFun hA 3) 2

theorem coords_4ab {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hA : M * AB4 = AB4 * M) :
    ∃ x0 x1 x2 x3 y0 y1 y2 y3 : ZMod 2,
      M = toM 4 (code4ab x0 x1 x2 x3 y0 y1 y2 y3) := by
  have h := eqCols_4ab hA
  have h0 : (fun k => M k 0) = ![M 0 0, M 1 0, M 2 0, M 3 0] := by
    funext k; fin_cases k <;> rfl
  have h2 : (fun k => M k 2) = ![M 0 2, M 1 2, M 2 2, M 3 2] := by
    funext k; fin_cases k <;> rfl
  rw [h0, h2] at h
  refine ⟨M 0 0, M 1 0, M 2 0, M 3 0, M 0 2, M 1 2, M 2 2, M 3 2, ?_⟩
  rw [toM_code_4ab]
  exact h

theorem hcode_4ab {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hA : M * AB4 = AB4 * M) :
    ∃ X, Bd 4 X ∧ toM 4 X = M ∧ chk 4 bits4 W4ab X = true := by
  obtain ⟨x0, x1, x2, x3, y0, y1, y2, y3, h⟩ := coords_4ab hA
  exact ⟨code4ab x0 x1 x2 x3 y0 y1 y2 y3, bd_4ab x0 x1 x2 x3 y0 y1 y2 y3, h.symm,
    chk_4ab x0 x1 x2 x3 y0 y1 y2 y3⟩

end CFSG.RankThree.PartTwo.Sec21.FF79.TLn
