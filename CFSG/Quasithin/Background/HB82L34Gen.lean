module

public import CFSG.Quasithin.Background.HZL34Gen

public section

namespace CFSG.Quasithin.H.L34Z

open CFSG.Fischer Matrix CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H13.Ch9.L34M

@[expose] def x2M : Matrix (Fin 3) (Fin 3) F4 := mc [0, 2, 2, 3, 0, 0, 0, 0, 1]

@[expose] def x2Mi : Matrix (Fin 3) (Fin 3) F4 := mc [0, 2, 0, 3, 0, 1, 0, 0, 1]

@[expose] def y2M : Matrix (Fin 3) (Fin 3) F4 := mc [2, 3, 0, 3, 0, 0, 0, 0, 3]

@[expose] def y2Mi : Matrix (Fin 3) (Fin 3) F4 := mc [0, 2, 0, 2, 1, 0, 0, 0, 2]

theorem xy2_inv_code : mcode (x2M * x2Mi) = mcode 1 ∧ mcode (x2Mi * x2M) = mcode 1 ∧
    mcode (y2M * y2Mi) = mcode 1 ∧ mcode (y2Mi * y2M) = mcode 1 := by
  decide +kernel

theorem x2_inv : x2M * x2Mi = 1 ∧ x2Mi * x2M = 1 :=
  ⟨mcode_injective xy2_inv_code.1, mcode_injective xy2_inv_code.2.1⟩

theorem y2_inv : y2M * y2Mi = 1 ∧ y2Mi * y2M = 1 :=
  ⟨mcode_injective xy2_inv_code.2.2.1, mcode_injective xy2_inv_code.2.2.2⟩

theorem det_x2M : x2M.det = 1 := by
  rw [Matrix.det_fin_three]
  exact f4_eq_of_code (by decide +kernel)

theorem det_y2M : y2M.det = 1 := by
  rw [Matrix.det_fin_three]
  exact f4_eq_of_code (by decide +kernel)

@[expose] def colsX2 : List ℕ := [2, 1, 69, 24, 16, 408, 144, 64, 97]

@[expose] def colsY2 : List ℕ := [27, 1, 4, 9, 24, 224, 288, 32, 64]

@[expose] def colsX2i : List ℕ := [2, 1, 134, 24, 16, 386, 128, 80, 120]

@[expose] def colsY2i : List ℕ := [2, 19, 4, 10, 26, 128, 256, 416, 192]

theorem cols_x2 : cols x2M = colsX2 ∧ cols y2M = colsY2 ∧ cols x2Mi = colsX2i ∧
    cols y2Mi = colsY2i := by
  decide +kernel

@[expose] def U0Basis : List ℕ := [1, 2, 8, 16]

theorem U0Basis_lt : ∀ a ∈ U0Basis, a < 2 ^ 9 := by
  decide +kernel

theorem l2_pres : ∀ m ∈ combos U0Basis, actM colsX2 m ∈ combos U0Basis ∧
    actM colsY2 m ∈ combos U0Basis ∧ actM colsX2i m ∈ combos U0Basis ∧
    actM colsY2i m ∈ combos U0Basis := by
  decide +kernel

theorem u_pres : ∀ t < 16, ∀ m ∈ combos U0Basis, actM (colsU.getD t []) m ∈ combos U0Basis := by
  decide +kernel

@[expose] def lAct2 (g m : ℕ) : ℕ := actM (if g = 0 then colsX2 else colsY2) m

@[expose] def cvData2 : List (ℕ × ℕ) :=
  [(0, 0), (0, 2), (0, 3), (0, 5), (0, 6), (0, 8), (1, 3), (1, 7)]

theorem cvData2_lt : ∀ e ∈ cvData2, e.2 < 9 := by
  decide +kernel

theorem w0_in_cv2 : ∀ w ∈ w0Basis,
    w ∈ combos (cvData2.map fun e => lAct2 e.1 (2 ^ e.2) ^^^ 2 ^ e.2) := by
  decide +kernel

theorem w0_notin : 32 ∈ combos w0Basis ∧ 32 ∉ combos U0Basis := by
  decide +kernel

@[expose] def c0M2 : Matrix (Fin 3) (Fin 3) F4 := x2M * y2M * x2Mi * y2Mi

@[expose] def c2M2 : Matrix (Fin 3) (Fin 3) F4 := x2M * (y2M * y2M) * x2Mi * (y2Mi * y2Mi)

@[expose] def xWord2 : List ℕ := [1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0]

@[expose] def yWord2 : List ℕ := [0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0]

theorem perfect2_words : cols (wM [c0M2, c2M2] xWord2) = colsX2 ∧
    cols (wM [c0M2, c2M2] yWord2) = colsY2 := by
  decide +kernel

end CFSG.Quasithin.H.L34Z
