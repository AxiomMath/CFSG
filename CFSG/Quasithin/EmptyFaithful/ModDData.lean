module

public import CFSG.Quasithin.Recognition.CertU33PresInputs

public section

namespace CFSG.Quasithin.ModD

open CFSG.CosetTable CFSG.Quasithin

@[expose] def vImg : Fin 5 → Equiv.Perm (Fin 63)
  | 0 => List.formPerm [1, 61, 36, 25] *
      List.formPerm [2, 8] *
      List.formPerm [3, 53, 38, 17] *
      List.formPerm [4, 33, 13, 39] *
      List.formPerm [5, 27, 42, 49] *
      List.formPerm [6, 41, 11, 31] *
      List.formPerm [7, 19, 40, 57] *
      List.formPerm [9, 59, 44, 23] *
      List.formPerm [10, 51, 46, 15] *
      List.formPerm [12, 29, 34, 47] *
      List.formPerm [14, 21, 32, 55] *
      List.formPerm [16, 52] *
      List.formPerm [18, 60] *
      List.formPerm [20, 22, 30, 28] *
      List.formPerm [24, 54] *
      List.formPerm [26, 62] *
      List.formPerm [37, 43] *
      List.formPerm [48, 50, 58, 56]
  | 1 => List.formPerm [1, 40, 3, 42] *
      List.formPerm [4, 11] *
      List.formPerm [5, 36, 7, 38] *
      List.formPerm [6, 13] *
      List.formPerm [9, 32, 10, 34] *
      List.formPerm [12, 44, 14, 46] *
      List.formPerm [15, 29, 23, 21] *
      List.formPerm [16, 54, 26, 60] *
      List.formPerm [17, 27, 25, 19] *
      List.formPerm [18, 52, 24, 62] *
      List.formPerm [20, 58, 30, 48] *
      List.formPerm [22, 56, 28, 50] *
      List.formPerm [31, 33] *
      List.formPerm [35, 45] *
      List.formPerm [37, 43] *
      List.formPerm [39, 41] *
      List.formPerm [47, 59, 55, 51] *
      List.formPerm [49, 61, 57, 53]
  | 2 => List.formPerm [1, 38] *
      List.formPerm [2, 35] *
      List.formPerm [4, 24] *
      List.formPerm [5, 61] *
      List.formPerm [6, 60] *
      List.formPerm [7, 25] *
      List.formPerm [8, 45] *
      List.formPerm [10, 44] *
      List.formPerm [11, 54] *
      List.formPerm [12, 15] *
      List.formPerm [13, 18] *
      List.formPerm [14, 51] *
      List.formPerm [16, 41] *
      List.formPerm [17, 40] *
      List.formPerm [20, 50] *
      List.formPerm [21, 47] *
      List.formPerm [23, 34] *
      List.formPerm [26, 31] *
      List.formPerm [27, 57] *
      List.formPerm [30, 56] *
      List.formPerm [32, 59] *
      List.formPerm [33, 62] *
      List.formPerm [39, 52] *
      List.formPerm [42, 53]
  | 3 => List.formPerm [1, 61, 42] *
      List.formPerm [2, 35, 43] *
      List.formPerm [3, 25, 7] *
      List.formPerm [4, 24, 28] *
      List.formPerm [5, 38, 53] *
      List.formPerm [6, 60, 48] *
      List.formPerm [8, 45, 37] *
      List.formPerm [9, 15, 12] *
      List.formPerm [10, 51, 32] *
      List.formPerm [11, 54, 58] *
      List.formPerm [13, 18, 22] *
      List.formPerm [14, 44, 59] *
      List.formPerm [16, 50, 33] *
      List.formPerm [17, 40, 36] *
      List.formPerm [20, 41, 62] *
      List.formPerm [21, 47, 55] *
      List.formPerm [23, 34, 46] *
      List.formPerm [26, 56, 39] *
      List.formPerm [27, 57, 49] *
      List.formPerm [30, 31, 52]
  | 4 => List.formPerm [0, 43, 37] *
      List.formPerm [1, 31, 32] *
      List.formPerm [2, 50, 48] *
      List.formPerm [3, 18, 15] *
      List.formPerm [4, 23, 27] *
      List.formPerm [5, 55, 60] *
      List.formPerm [6, 42, 44] *
      List.formPerm [7, 10, 11] *
      List.formPerm [8, 30, 22] *
      List.formPerm [9, 62, 53] *
      List.formPerm [12, 38, 41] *
      List.formPerm [13, 51, 57] *
      List.formPerm [14, 19, 26] *
      List.formPerm [16, 34, 49] *
      List.formPerm [17, 47, 33] *
      List.formPerm [20, 58, 45] *
      List.formPerm [21, 39, 61] *
      List.formPerm [24, 59, 36] *
      List.formPerm [25, 46, 52] *
      List.formPerm [28, 35, 56] *
      List.formPerm [29, 54, 40]

@[expose] def lImg : Fin 5 → Equiv.Perm (Fin 63)
  | 0 => List.formPerm [1, 28, 40, 54] *
      List.formPerm [2, 18, 37, 30] *
      List.formPerm [3, 33, 59, 53] *
      List.formPerm [5, 16, 6, 10] *
      List.formPerm [7, 24, 56, 42] *
      List.formPerm [8, 17, 32, 29] *
      List.formPerm [9, 38, 47, 41] *
      List.formPerm [11, 27, 35, 20] *
      List.formPerm [12, 23, 34, 14] *
      List.formPerm [13, 26, 61, 58] *
      List.formPerm [15, 36, 48, 43] *
      List.formPerm [19, 22, 45, 50] *
      List.formPerm [21, 31, 60, 51] *
      List.formPerm [46, 49, 62, 57]
  | 1 => List.formPerm [1, 60, 7, 48] *
      List.formPerm [2, 27, 8, 23] *
      List.formPerm [3, 45, 9, 61] *
      List.formPerm [11, 29, 12, 30] *
      List.formPerm [13, 59, 19, 47] *
      List.formPerm [14, 37, 20, 32] *
      List.formPerm [15, 40, 21, 56] *
      List.formPerm [17, 34, 18, 35] *
      List.formPerm [22, 41, 26, 53] *
      List.formPerm [24, 43, 28, 51] *
      List.formPerm [31, 42, 36, 54] *
      List.formPerm [33, 50, 38, 58] *
      List.formPerm [39, 52, 55, 44] *
      List.formPerm [46, 57, 62, 49]
  | 2 => List.formPerm [1, 32] *
      List.formPerm [2, 56] *
      List.formPerm [3, 47] *
      List.formPerm [4, 25] *
      List.formPerm [5, 55] *
      List.formPerm [6, 39] *
      List.formPerm [7, 8] *
      List.formPerm [10, 52] *
      List.formPerm [11, 31] *
      List.formPerm [12, 51] *
      List.formPerm [13, 33] *
      List.formPerm [14, 28] *
      List.formPerm [15, 18] *
      List.formPerm [16, 44] *
      List.formPerm [17, 48] *
      List.formPerm [19, 53] *
      List.formPerm [20, 54] *
      List.formPerm [21, 30] *
      List.formPerm [23, 24] *
      List.formPerm [26, 50] *
      List.formPerm [27, 42] *
      List.formPerm [29, 60] *
      List.formPerm [34, 43] *
      List.formPerm [35, 36] *
      List.formPerm [37, 40] *
      List.formPerm [38, 61] *
      List.formPerm [41, 45] *
      List.formPerm [46, 62]
  | 3 => List.formPerm [0, 4, 25] *
      List.formPerm [1, 33, 23] *
      List.formPerm [2, 28, 61] *
      List.formPerm [3, 18, 48] *
      List.formPerm [5, 39, 62] *
      List.formPerm [6, 55, 46] *
      List.formPerm [7, 53, 20] *
      List.formPerm [8, 54, 19] *
      List.formPerm [9, 30, 21] *
      List.formPerm [10, 52, 57] *
      List.formPerm [11, 31, 22] *
      List.formPerm [12, 51, 58] *
      List.formPerm [13, 32, 24] *
      List.formPerm [14, 56, 38] *
      List.formPerm [15, 47, 17] *
      List.formPerm [16, 44, 49] *
      List.formPerm [26, 35, 43] *
      List.formPerm [27, 40, 41] *
      List.formPerm [29, 60, 59] *
      List.formPerm [34, 36, 50] *
      List.formPerm [37, 42, 45]
  | 4 => List.formPerm [1, 8, 43] *
      List.formPerm [3, 5, 41] *
      List.formPerm [4, 62, 49] *
      List.formPerm [6, 33, 47] *
      List.formPerm [7, 36, 11] *
      List.formPerm [9, 44, 13] *
      List.formPerm [10, 19, 26] *
      List.formPerm [14, 18, 48] *
      List.formPerm [16, 61, 50] *
      List.formPerm [17, 23, 42] *
      List.formPerm [20, 28, 30] *
      List.formPerm [21, 27, 29] *
      List.formPerm [22, 55, 38] *
      List.formPerm [25, 46, 57] *
      List.formPerm [31, 56, 37] *
      List.formPerm [34, 40, 51] *
      List.formPerm [39, 53, 58] *
      List.formPerm [45, 59, 52]

@[expose] def evalW (g : Fin 5 → Equiv.Perm (Fin 63)) (w : List (Fin 5 × Bool)) : Equiv.Perm (Fin 63) :=
  (w.map fun l => cond l.2 (g l.1) (g l.1)⁻¹).prod

@[expose] def vTbl : List (List ℕ) :=
  [[0, 61, 8, 53, 33, 27, 41, 19, 2, 59, 51, 31, 29, 39, 21, 10, 52, 3, 60, 40, 22, 32, 30, 9, 54, 1, 62, 42, 20, 34, 28, 6, 55, 13, 47, 35, 25, 43, 17, 4, 57, 11, 49, 37, 23, 45, 15, 12, 50, 5, 58, 46, 16, 38, 24, 14, 48, 7, 56, 44, 18, 36, 26],
    [0, 40, 2, 42, 11, 36, 13, 38, 8, 32, 34, 4, 44, 6, 46, 29, 54, 27, 52, 17, 58, 15, 56, 21, 62, 19, 60, 25, 50, 23, 48, 33, 10, 31, 9, 45, 7, 43, 5, 41, 3, 39, 1, 37, 14, 35, 12, 59, 20, 61, 22, 47, 24, 49, 26, 51, 28, 53, 30, 55, 16, 57, 18],
    [0, 38, 35, 3, 24, 61, 60, 25, 45, 9, 44, 54, 15, 18, 51, 12, 41, 40, 13, 19, 50, 47, 22, 34, 4, 7, 31, 57, 28, 29, 56, 26, 59, 62, 23, 2, 36, 37, 1, 52, 17, 16, 53, 43, 10, 8, 46, 21, 48, 49, 20, 14, 39, 42, 11, 55, 30, 27, 58, 32, 6, 5, 33],
    [0, 61, 35, 25, 24, 38, 60, 3, 45, 15, 51, 54, 9, 18, 44, 12, 50, 40, 22, 19, 41, 47, 13, 34, 28, 7, 56, 57, 4, 29, 31, 52, 10, 16, 46, 43, 17, 8, 53, 26, 36, 62, 1, 2, 59, 37, 23, 55, 6, 27, 33, 32, 30, 5, 58, 21, 39, 49, 11, 14, 48, 42, 20],
    [43, 31, 50, 18, 23, 55, 42, 10, 30, 62, 11, 7, 38, 51, 19, 3, 34, 47, 15, 26, 58, 39, 8, 27, 59, 46, 14, 4, 35, 54, 22, 32, 1, 17, 49, 56, 24, 0, 41, 61, 29, 12, 44, 37, 6, 20, 52, 33, 2, 16, 48, 57, 25, 9, 40, 60, 28, 13, 45, 36, 5, 21, 53]]

@[expose] def vTblInv : List (List ℕ) :=
  [[0, 25, 8, 17, 39, 49, 31, 57, 2, 23, 15, 41, 47, 33, 55, 46, 52, 38, 60, 7, 28, 14, 20, 44, 54, 36, 62, 5, 30, 12, 22, 11, 21, 4, 29, 35, 61, 43, 53, 13, 19, 6, 27, 37, 59, 45, 51, 34, 56, 42, 48, 10, 16, 3, 24, 32, 58, 40, 50, 9, 18, 1, 26],
    [0, 42, 2, 40, 11, 38, 13, 36, 8, 34, 32, 4, 46, 6, 44, 21, 60, 19, 62, 25, 48, 23, 50, 29, 52, 27, 54, 17, 56, 15, 58, 33, 9, 31, 10, 45, 5, 43, 7, 41, 1, 39, 3, 37, 12, 35, 14, 51, 30, 53, 28, 55, 18, 57, 16, 59, 22, 61, 20, 47, 26, 49, 24],
    [0, 38, 35, 3, 24, 61, 60, 25, 45, 9, 44, 54, 15, 18, 51, 12, 41, 40, 13, 19, 50, 47, 22, 34, 4, 7, 31, 57, 28, 29, 56, 26, 59, 62, 23, 2, 36, 37, 1, 52, 17, 16, 53, 43, 10, 8, 46, 21, 48, 49, 20, 14, 39, 42, 11, 55, 30, 27, 58, 32, 6, 5, 33],
    [0, 42, 43, 7, 28, 53, 48, 25, 37, 12, 32, 58, 15, 22, 59, 9, 33, 36, 13, 19, 62, 55, 18, 46, 4, 3, 39, 49, 24, 29, 52, 30, 51, 50, 23, 2, 40, 45, 5, 56, 17, 20, 61, 35, 14, 8, 34, 21, 60, 57, 16, 10, 31, 38, 11, 47, 26, 27, 54, 44, 6, 1, 41],
    [37, 32, 48, 15, 27, 60, 44, 11, 22, 53, 7, 10, 41, 57, 26, 18, 49, 33, 3, 14, 45, 61, 30, 4, 36, 52, 19, 23, 56, 40, 8, 1, 31, 47, 16, 28, 59, 43, 12, 21, 54, 38, 6, 0, 42, 58, 25, 17, 50, 34, 2, 13, 46, 62, 29, 5, 35, 51, 20, 24, 55, 39, 9]]

@[expose] def lTbl : List (List ℕ) :=
  [[0, 28, 18, 33, 4, 16, 10, 24, 17, 38, 5, 27, 23, 26, 12, 36, 6, 32, 37, 22, 11, 31, 45, 34, 56, 25, 61, 35, 40, 8, 2, 60, 29, 59, 14, 20, 48, 30, 47, 39, 54, 9, 7, 15, 44, 50, 49, 41, 43, 62, 19, 21, 52, 3, 1, 55, 42, 46, 13, 53, 51, 58, 57],
    [0, 60, 27, 45, 4, 5, 6, 48, 23, 61, 10, 29, 30, 59, 37, 40, 16, 34, 35, 47, 32, 56, 41, 2, 43, 25, 53, 8, 51, 12, 11, 42, 14, 50, 18, 17, 54, 20, 58, 52, 21, 26, 36, 28, 39, 9, 57, 13, 1, 46, 38, 24, 55, 22, 31, 44, 15, 62, 33, 19, 7, 3, 49],
    [0, 32, 56, 47, 25, 55, 39, 8, 7, 9, 52, 31, 51, 33, 28, 18, 44, 48, 15, 53, 54, 30, 22, 24, 23, 4, 50, 42, 14, 60, 21, 11, 1, 13, 43, 36, 35, 40, 61, 6, 37, 45, 27, 34, 16, 41, 62, 3, 17, 49, 26, 12, 10, 19, 20, 5, 2, 57, 58, 59, 29, 38, 46],
    [4, 33, 28, 18, 25, 39, 55, 53, 54, 30, 52, 31, 51, 32, 56, 47, 44, 15, 48, 8, 7, 9, 11, 1, 13, 0, 35, 40, 61, 60, 21, 22, 24, 23, 36, 43, 50, 42, 14, 62, 41, 27, 45, 26, 49, 37, 6, 17, 3, 16, 34, 58, 57, 20, 19, 46, 38, 10, 12, 29, 59, 2, 5],
    [0, 8, 2, 5, 62, 41, 33, 36, 43, 44, 19, 7, 12, 9, 18, 15, 61, 23, 48, 26, 28, 27, 55, 42, 24, 46, 10, 29, 30, 21, 20, 56, 32, 47, 40, 35, 11, 31, 22, 53, 51, 3, 17, 1, 13, 59, 57, 6, 14, 4, 16, 34, 45, 58, 54, 38, 37, 25, 39, 52, 60, 50, 49]]

@[expose] def lTblInv : List (List ℕ) :=
  [[0, 54, 30, 53, 4, 10, 16, 42, 29, 41, 6, 20, 14, 58, 34, 43, 5, 8, 2, 50, 35, 51, 19, 12, 7, 25, 13, 11, 1, 32, 37, 21, 17, 3, 23, 27, 15, 18, 9, 39, 28, 47, 56, 48, 44, 22, 57, 38, 36, 46, 45, 60, 52, 59, 40, 55, 24, 62, 61, 33, 31, 26, 49],
    [0, 48, 23, 61, 4, 5, 6, 60, 27, 45, 10, 30, 29, 47, 32, 56, 16, 35, 34, 59, 37, 40, 53, 8, 51, 25, 41, 2, 43, 11, 12, 54, 20, 58, 17, 18, 42, 14, 50, 44, 15, 22, 31, 24, 55, 3, 49, 19, 7, 62, 33, 28, 39, 26, 36, 52, 21, 46, 38, 13, 1, 9, 57],
    [0, 32, 56, 47, 25, 55, 39, 8, 7, 9, 52, 31, 51, 33, 28, 18, 44, 48, 15, 53, 54, 30, 22, 24, 23, 4, 50, 42, 14, 60, 21, 11, 1, 13, 43, 36, 35, 40, 61, 6, 37, 45, 27, 34, 16, 41, 62, 3, 17, 49, 26, 12, 10, 19, 20, 5, 2, 57, 58, 59, 29, 38, 46],
    [25, 23, 61, 48, 0, 62, 46, 20, 19, 21, 57, 22, 58, 24, 38, 17, 49, 47, 3, 54, 53, 30, 31, 33, 32, 4, 43, 41, 2, 59, 9, 11, 13, 1, 50, 26, 34, 45, 56, 5, 27, 40, 37, 35, 16, 42, 55, 15, 18, 44, 36, 12, 10, 7, 8, 6, 14, 52, 51, 60, 29, 28, 39],
    [0, 43, 2, 41, 49, 3, 47, 11, 1, 13, 26, 36, 12, 44, 48, 15, 50, 42, 14, 10, 30, 29, 38, 17, 24, 57, 19, 21, 20, 27, 28, 37, 32, 6, 51, 35, 7, 56, 55, 58, 34, 5, 23, 8, 9, 52, 25, 33, 18, 62, 61, 40, 59, 39, 54, 22, 31, 46, 53, 45, 60, 16, 4]]

@[expose] def evalN (T U : List (List ℕ)) : List (Fin 5 × Bool) → ℕ → ℕ
  | [], x => x
  | l :: w, x => ((cond l.2 T U).getD l.1 []).getD (evalN T U w x) 0

theorem evalW_val_eq_evalN {g : Fin 5 → Equiv.Perm (Fin 63)} {T U : List (List ℕ)}
    (hT : ∀ i : Fin 5, ∀ x : Fin 63, ((g i x : Fin 63) : ℕ) = (T.getD i []).getD x 0)
    (hU : ∀ i : Fin 5, ∀ x : Fin 63, (((g i)⁻¹ x : Fin 63) : ℕ) = (U.getD i []).getD x 0)
    (w : List (Fin 5 × Bool)) (x : Fin 63) : ((evalW g w x : Fin 63) : ℕ) = evalN T U w x := by
  induction w with
  | nil => simp [evalW, evalN]
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    have e : evalW g ((i, b) :: w) = cond b (g i) (g i)⁻¹ * evalW g w := by
      simp [evalW]
    rw [e, Equiv.Perm.mul_apply, evalN, ← ih]
    cases b
    · exact hU i _
    · exact hT i _

theorem evalW_eq_one_of_evalN {g : Fin 5 → Equiv.Perm (Fin 63)} {T U : List (List ℕ)}
    (hT : ∀ i : Fin 5, ∀ x : Fin 63, ((g i x : Fin 63) : ℕ) = (T.getD i []).getD x 0)
    (hU : ∀ i : Fin 5, ∀ x : Fin 63, (((g i)⁻¹ x : Fin 63) : ℕ) = (U.getD i []).getD x 0)
    {w : List (Fin 5 × Bool)} (h : ∀ x : Fin 63, evalN T U w x = x) : evalW g w = 1 := by
  ext x
  rw [evalW_val_eq_evalN hT hU, h x]
  rfl

theorem vTbl_spec : ∀ i : Fin 5, ∀ x : Fin 63, ((vImg i x : Fin 63) : ℕ) = (vTbl.getD i []).getD x 0 := by
  decide +kernel

theorem vTblInv_spec :
    ∀ i : Fin 5, ∀ x : Fin 63, (((vImg i)⁻¹ x : Fin 63) : ℕ) = (vTblInv.getD i []).getD x 0 := by
  decide +kernel

theorem lTbl_spec : ∀ i : Fin 5, ∀ x : Fin 63, ((lImg i x : Fin 63) : ℕ) = (lTbl.getD i []).getD x 0 := by
  decide +kernel

theorem lTblInv_spec :
    ∀ i : Fin 5, ∀ x : Fin 63, (((lImg i)⁻¹ x : Fin 63) : ℕ) = (lTblInv.getD i []).getD x 0 := by
  decide +kernel

theorem vTbl_relators : ∀ w ∈ u33PresRels, ∀ x : Fin 63, evalN vTbl vTblInv w x = x := by
  decide +kernel

theorem lTbl_relators : ∀ w ∈ u33PresRels, ∀ x : Fin 63, evalN lTbl lTblInv w x = x := by
  decide +kernel

theorem vImg_relators : ∀ w ∈ u33PresRels, evalW vImg w = 1 := fun w hw =>
  evalW_eq_one_of_evalN vTbl_spec vTblInv_spec (vTbl_relators w hw)

theorem lImg_relators : ∀ w ∈ u33PresRels, evalW lImg w = 1 := fun w hw =>
  evalW_eq_one_of_evalN lTbl_spec lTblInv_spec (lTbl_relators w hw)

noncomputable def vHom : PG 5 u33PresRels →* Equiv.Perm (Fin 63) :=
  PresentedGroup.toGroup (f := vImg) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [FreeGroup.lift_mk]
    exact vImg_relators w hw)

noncomputable def lHom : PG 5 u33PresRels →* Equiv.Perm (Fin 63) :=
  PresentedGroup.toGroup (f := lImg) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [FreeGroup.lift_mk]
    exact lImg_relators w hw)

theorem vHom_of (i : Fin 5) : vHom (PresentedGroup.of i) = vImg i := by
  rw [vHom, PresentedGroup.toGroup.of]

theorem lHom_of (i : Fin 5) : lHom (PresentedGroup.of i) = lImg i := by
  rw [lHom, PresentedGroup.toGroup.of]

@[expose] def vTab : List String := ["", "YxyxY", "xy", "YXYxY", "xYXy", "yXYxy", "xYxy", "yxYXY", "xY", "YXyXY", "YxYXY", "xYXY", "yxyXY", "xYxY", "yXyXy", "yXYxY", "Xyxy", "yxyxy", "XYxY", "YXyXy", "yXY", "YxyXy", "YxY", "yxYXy", "XYXy", "yXyxY", "XyXy", "YxYXy", "YXy", "YXYXY", "yxY", "xyxY", "yxyxY", "xyxy", "yXyxy", "Xy", "YXYXy", "Y", "YxyXY", "xyXy", "yXYXY", "xyXY", "yxYxy", "y", "YxYxy", "XY", "YXyxY", "Yxyxy", "Yxy", "YXyxy", "yxy", "yxYxY", "XyxY", "yXyXY", "XYXY", "YXYxy", "yXy", "YxYxY", "YXY", "yXYXy", "XYxy", "yxyXy", "XyXY"]

@[expose] def lTab : List String := ["", "XyxyX", "xyxYx", "Yxyx", "x", "xyx", "xyX", "XyXyx", "xyxYX", "YXYx", "xYX", "xYXyX", "xYXyx", "yXYx", "xyXyX", "XYxyX", "xYx", "xYxyX", "xYxyx", "yxYX", "xyXyx", "XYXYx", "YXyX", "xyxyX", "XyXYx", "X", "YxYX", "xyxyx", "XyxYx", "xYXYX", "xYXYx", "XYXyX", "xyXYx", "yxyX", "xYxYx", "xYxYX", "XYxYx", "xyXYX", "yXyX", "Xyx", "Xyxyx", "yxyx", "XyXYX", "XYxYX", "XYx", "yXYX", "yX", "YxyX", "XYxyx", "Yx", "YxYx", "XYXyx", "XYX", "yXyx", "XyxYX", "XyX", "XyXyX", "YX", "YXyx", "YXYX", "XYXYX", "yxYx", "yx"]

theorem vTab_spec : ∀ j : Fin 63, evalW vImg (u33Word (vTab.getD j.val "")) 0 = j := by decide +kernel

theorem lTab_spec : ∀ j : Fin 63, evalW lImg (u33Word (lTab.getD j.val "")) 0 = j := by decide +kernel

theorem vImg_fix : vImg 0 0 = 0 ∧ vImg 1 0 = 0 ∧ vImg 2 0 = 0 ∧ vImg 3 0 = 0 := by decide +kernel

theorem lImg_fix : lImg 0 0 = 0 ∧ lImg 1 0 = 0 ∧ lImg 2 0 = 0 ∧ lImg 4 0 = 0 := by decide +kernel

@[expose] def cSet : List (Fin 63) := [0, 2, 8, 35, 37, 43, 45]

theorem fl_noPair : ∀ p q : Fin 63, p ≠ 0 → q ≠ 0 → p ≠ q →
    ¬ (∀ i ∈ [(0 : Fin 5), 1, 2, 3], (vImg i p = p ∨ vImg i p = q) ∧ (vImg i q = p ∨ vImg i q = q)) := by
  decide +kernel

theorem lImg_four_fix : (Finset.univ.filter fun i : Fin 63 => lImg 4 i = i).card = 9 := by decide +kernel

end CFSG.Quasithin.ModD
