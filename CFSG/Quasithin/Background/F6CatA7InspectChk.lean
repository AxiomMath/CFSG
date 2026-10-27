module

public import CFSG.Quasithin.Background.F6CatInspect

public section

namespace CFSG.Quasithin.F6.A7Insp

open Equiv CFSG.Sporadic.Bridge

@[expose] def gen (i : ℕ) : Perm (Fin 7) :=
  if i = 0 then swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5 * swap 5 6
  else swap 0 1 * swap 1 2

@[expose] def gL (i : ℕ) : List ℕ :=
  if i = 0 then [1, 2, 3, 4, 5, 6, 0] else [1, 2, 0, 3, 4, 5, 6]

@[expose] def giL (i : ℕ) : List ℕ :=
  if i = 0 then [6, 0, 1, 2, 3, 4, 5] else [2, 0, 1, 3, 4, 5, 6]

theorem gen_chk : RepL (gL 0) (gen 0) ∧ RepL (gL 1) (gen 1) ∧ RepL (giL 0) (gen 0)⁻¹ ∧
    RepL (giL 1) (gen 1)⁻¹ := by decide

@[expose] def idL : List ℕ := List.range 7

@[expose] def wR : List (ℕ × Bool) :=
  [(0, false), (0, false), (1, false), (0, false), (1, true), (0, false), (0, false),
    (0, false)]

@[expose] def r : Perm (Fin 7) := wordProd gen wR

@[expose] def rL : List ℕ := [1, 2, 3, 0, 5, 4, 6]

@[expose] def wF : List (ℕ × Bool) :=
  [(0, true), (0, true), (0, true), (1, false), (0, false), (1, false), (0, false), (1, false),
    (0, false), (1, true)]

@[expose] def f : Perm (Fin 7) := wordProd gen wF

@[expose] def fL : List ℕ := [2, 1, 0, 3, 5, 4, 6]

theorem tgen_chk :
    rL = F6.wordLst gL giL 7 wR ∧
    fL = F6.wordLst gL giL 7 wF := by
  decide +kernel

@[expose] def tel (a : ℕ) : Perm (Fin 7) := r ^ (a % 4) * f ^ (a / 4)

@[expose] def telTab : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6], [1, 2, 3, 0, 5, 4, 6], [2, 3, 0, 1, 4, 5, 6], [3, 0, 1, 2, 5, 4, 6],
    [2, 1, 0, 3, 5, 4, 6], [3, 2, 1, 0, 4, 5, 6], [0, 3, 2, 1, 5, 4, 6], [1, 0, 3, 2, 4, 5, 6]]

@[expose] def telL (a : ℕ) : List ℕ := telTab.getD a []

theorem telL_chk : ∀ a < 8,
    telL a = compL (powLst 7 rL (a % 4)) (powLst 7 fL (a / 4)) := by
  decide +kernel

theorem telL_inj_chk : ∀ a < 8, ∀ b < 8, telL a = telL b → a = b := by decide +kernel

@[expose] def trR : List ℕ := [1, 2, 3, 0, 7, 4, 5, 6]

@[expose] def trF : List ℕ := [4, 5, 6, 7, 0, 1, 2, 3]

theorem tr_chk : ∀ a < 8,
    trR.getD a 0 < 8 ∧ compL (telL a) rL = telL (trR.getD a 0) ∧
    trF.getD a 0 < 8 ∧ compL (telL a) fL = telL (trF.getD a 0) := by
  decide +kernel

@[expose] def dWTab : List (List (ℕ × Bool)) :=
  [[],
    [(1, true)],
    [(0, true)],
    [(0, false)],
    [(1, false), (0, true)],
    [(0, false), (1, true)],
    [(0, false), (1, false)],
    [(1, true), (0, true)],
    [(0, true), (0, true)],
    [(0, false), (0, false)],
    [(1, false), (0, true), (0, true)],
    [(0, false), (1, true), (0, true)],
    [(0, true), (0, true), (1, true)],
    [(0, true), (0, true), (0, true)],
    [(0, true), (0, true), (1, false)],
    [(0, false), (0, false), (0, false)],
    [(0, false), (1, false), (0, false)],
    [(1, true), (0, false), (0, false)],
    [(1, false), (0, false), (0, false)],
    [(0, false), (1, false), (0, true), (0, true)],
    [(0, true), (1, true), (0, true), (1, true)],
    [(0, true), (1, true), (0, true), (0, true)],
    [(0, false), (1, true), (0, true), (1, false)],
    [(0, false), (0, false), (1, false), (0, false)],
    [(1, false), (0, true), (0, true), (1, false)],
    [(1, false), (0, false), (1, false), (0, false)],
    [(1, true), (0, false), (1, false), (0, false)],
    [(0, false), (0, false), (1, false), (0, true)],
    [(1, true), (0, false), (1, false), (0, true), (0, true)],
    [(1, true), (0, false), (0, false), (1, true), (0, true)],
    [(0, false), (1, true), (0, false), (1, true), (0, true)],
    [(0, false), (1, true), (0, true), (1, false), (0, true)],
    [(0, false), (1, true), (0, true), (0, true), (0, true)],
    [(0, false), (1, false), (0, true), (1, true), (0, true)],
    [(0, false), (0, false), (1, true), (0, false), (0, false)],
    [(1, true), (0, false), (0, false), (1, false), (0, false)],
    [(1, true), (0, false), (0, false), (1, false), (0, true)],
    [(1, true), (0, false), (1, true), (0, true), (0, true), (1, true)],
    [(1, true), (0, false), (1, false), (0, true), (1, true), (0, true)],
    [(0, false), (1, true), (0, false), (1, false), (0, true), (1, true)],
    [(0, false), (0, false), (1, true), (0, true), (1, true), (0, true)],
    [(0, false), (0, false), (1, true), (0, true), (0, true), (0, true)],
    [(0, true), (0, true), (1, true), (0, false), (1, false), (0, true)],
    [(1, false), (0, false), (1, true), (0, true), (0, true), (0, true)],
    [(0, true), (0, true), (1, false), (0, false), (1, true), (0, true)],
    [(0, false), (1, true), (0, true), (0, true), (0, true), (1, true)],
    [(0, true), (0, true), (1, false), (0, false), (0, false), (1, false), (0, true)],
    [(0, false), (0, false), (1, true), (0, true), (1, true), (0, true), (1, true)],
    [(1, false), (0, false), (1, true), (0, true), (0, true), (0, true), (1, true)]]

@[expose] def d (j : ℕ) : Perm (Fin 7) := wordProd gen (dWTab.getD j [])

@[expose] def dTab : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6], [1, 2, 0, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6, 0], [6, 0, 1, 2, 3, 4, 5],
    [0, 1, 3, 4, 5, 6, 2], [0, 1, 6, 2, 3, 4, 5], [1, 6, 0, 2, 3, 4, 5], [2, 0, 3, 4, 5, 6, 1],
    [2, 3, 4, 5, 6, 0, 1], [5, 6, 0, 1, 2, 3, 4], [1, 3, 4, 5, 6, 2, 0], [1, 6, 2, 3, 4, 5, 0],
    [3, 4, 2, 5, 6, 0, 1], [3, 4, 5, 6, 0, 1, 2], [4, 2, 3, 5, 6, 0, 1], [4, 5, 6, 0, 1, 2, 3],
    [5, 1, 6, 0, 2, 3, 4], [5, 6, 1, 2, 0, 3, 4], [5, 6, 2, 0, 1, 3, 4], [0, 2, 3, 4, 5, 1, 6],
    [1, 4, 3, 5, 6, 0, 2], [1, 4, 5, 6, 0, 2, 3], [2, 1, 6, 3, 4, 5, 0], [4, 0, 5, 6, 1, 2, 3],
    [4, 1, 3, 5, 6, 2, 0], [5, 0, 6, 2, 1, 3, 4], [5, 2, 6, 1, 0, 3, 4], [5, 6, 1, 2, 3, 4, 0],
    [1, 0, 3, 4, 5, 2, 6], [1, 5, 2, 0, 3, 4, 6], [1, 5, 6, 2, 3, 4, 0], [1, 6, 3, 4, 5, 0, 2],
    [2, 3, 4, 5, 0, 1, 6], [2, 6, 3, 4, 5, 1, 0], [3, 4, 6, 0, 5, 1, 2], [4, 1, 5, 6, 2, 0, 3],
    [5, 6, 2, 0, 3, 4, 1], [0, 3, 6, 4, 5, 1, 2], [0, 6, 3, 4, 5, 2, 1], [0, 6, 5, 2, 3, 4, 1],
    [1, 0, 2, 3, 4, 6, 5], [1, 2, 3, 4, 6, 0, 5], [1, 3, 2, 5, 6, 0, 4], [1, 3, 4, 5, 2, 0, 6],
    [2, 1, 3, 5, 6, 0, 4], [3, 4, 2, 5, 0, 1, 6], [0, 1, 2, 3, 5, 6, 4], [0, 2, 1, 3, 4, 6, 5],
    [3, 4, 1, 5, 2, 0, 6]]

@[expose] def dL (j : ℕ) : List ℕ := dTab.getD j []

theorem dL_chk : ∀ j < 49, dL j = F6.wordLst gL giL 7 (dWTab.getD j []) := by decide +kernel

theorem d_zero_chk : dWTab.getD 0 [] = [] := by decide +kernel

@[expose] def decTab : List (List ℕ) :=
  [[0, 2, 0, 7, 1, 2, 1, 2, 0, 4, 1, 2, 2, 2, 0, 7, 1, 7, 3, 2, 0, 4, 1, 7, 4, 2, 0, 4, 1, 0,
      5, 2, 0, 7, 1, 5, 6, 2, 0, 4, 1, 5, 7, 2, 0, 7, 1, 0],
    [0, 7, 0, 4, 1, 4, 6, 4, 0, 7, 0, 1, 7, 7, 0, 4, 1, 3, 1, 4, 0, 7, 0, 6, 4, 4, 0, 7, 0, 3,
      2, 7, 0, 4, 1, 1, 3, 4, 0, 7, 0, 4, 5, 7, 0, 4, 1, 6],
    [0, 8, 0, 2, 4, 0, 0, 31, 2, 7, 7, 6, 6, 14, 5, 2, 4, 5, 1, 3, 1, 7, 7, 1, 7, 37, 7, 7, 7,
      4, 6, 41, 0, 2, 4, 7, 1, 27, 6, 7, 7, 3, 0, 20, 0, 2, 4, 2],
    [7, 0, 7, 0, 5, 0, 2, 34, 6, 0, 6, 6, 7, 22, 5, 0, 5, 5, 4, 30, 2, 0, 6, 1, 5, 31, 4, 0, 6,
      4, 2, 11, 5, 0, 5, 7, 7, 28, 4, 0, 6, 3, 6, 11, 1, 0, 5, 2],
    [0, 10, 0, 5, 7, 0, 0, 38, 2, 2, 2, 6, 2, 14, 0, 5, 7, 5, 3, 6, 6, 2, 2, 1, 3, 30, 3, 2, 2,
      4, 2, 42, 0, 5, 7, 7, 3, 36, 6, 2, 2, 3, 4, 12, 2, 5, 7, 2],
    [0, 11, 0, 0, 6, 0, 4, 39, 7, 0, 3, 6, 4, 1, 4, 0, 6, 5, 4, 27, 5, 0, 3, 1, 2, 19, 4, 0, 3,
      4, 4, 22, 4, 0, 6, 7, 7, 38, 4, 0, 3, 3, 1, 11, 3, 0, 6, 2],
    [7, 11, 7, 0, 3, 0, 4, 29, 2, 0, 5, 6, 0, 22, 0, 0, 3, 5, 2, 33, 4, 0, 5, 1, 2, 37, 4, 0,
      5, 4, 4, 11, 4, 0, 3, 7, 4, 36, 5, 0, 5, 3, 7, 1, 2, 0, 3, 2],
    [1, 8, 7, 7, 2, 0, 0, 33, 2, 5, 4, 6, 3, 24, 5, 7, 2, 5, 6, 5, 3, 5, 4, 1, 6, 39, 6, 5, 4,
      4, 7, 44, 0, 7, 2, 7, 0, 34, 7, 5, 4, 3, 7, 12, 0, 7, 2, 2],
    [0, 13, 0, 0, 12, 0, 3, 10, 5, 0, 14, 6, 5, 9, 6, 0, 12, 5, 1, 44, 7, 0, 14, 1, 1, 41, 7,
      0, 14, 4, 1, 17, 6, 0, 12, 7, 1, 8, 2, 0, 14, 3, 4, 15, 3, 0, 12, 2],
    [0, 3, 0, 7, 16, 4, 6, 28, 1, 7, 9, 5, 0, 30, 0, 7, 16, 3, 7, 27, 0, 7, 9, 0, 7, 36, 7, 7,
      9, 7, 0, 39, 0, 7, 16, 1, 7, 5, 0, 7, 9, 2, 0, 29, 7, 7, 16, 6],
    [2, 21, 0, 4, 20, 2, 6, 8, 5, 0, 24, 6, 7, 18, 6, 4, 20, 7, 6, 42, 7, 0, 24, 1, 0, 42, 7,
      0, 24, 4, 3, 18, 6, 4, 20, 5, 0, 8, 5, 0, 24, 3, 4, 21, 0, 4, 20, 0],
    [1, 27, 1, 6, 11, 1, 5, 29, 6, 0, 22, 6, 1, 39, 3, 6, 11, 6, 3, 33, 0, 0, 22, 1, 5, 36, 1,
      0, 22, 4, 2, 38, 0, 6, 11, 4, 3, 37, 0, 0, 22, 3, 7, 19, 0, 6, 11, 3],
    [4, 23, 4, 0, 14, 0, 7, 44, 2, 0, 8, 6, 3, 23, 0, 0, 14, 5, 1, 42, 2, 0, 8, 1, 1, 12, 5, 0,
      8, 4, 1, 26, 3, 0, 14, 7, 7, 20, 5, 0, 8, 3, 2, 16, 7, 0, 14, 2],
    [0, 15, 0, 3, 15, 7, 7, 18, 0, 3, 23, 6, 3, 16, 2, 3, 15, 2, 0, 43, 1, 3, 23, 1, 1, 25, 6,
      3, 23, 4, 1, 32, 2, 3, 15, 0, 0, 21, 5, 3, 23, 3, 2, 17, 4, 3, 15, 5],
    [2, 9, 2, 0, 8, 0, 1, 14, 7, 0, 12, 6, 7, 13, 4, 0, 8, 5, 7, 41, 5, 0, 12, 1, 3, 24, 2, 0,
      12, 4, 6, 17, 2, 0, 8, 7, 7, 42, 5, 0, 12, 3, 3, 15, 7, 0, 8, 2],
    [0, 9, 0, 0, 23, 2, 4, 25, 2, 1, 13, 3, 5, 32, 1, 0, 23, 7, 5, 21, 1, 1, 13, 4, 3, 43, 2,
      1, 13, 1, 2, 13, 5, 0, 23, 5, 2, 18, 4, 1, 13, 6, 4, 26, 0, 0, 23, 0],
    [0, 6, 0, 7, 9, 4, 1, 33, 1, 0, 9, 1, 6, 19, 6, 7, 9, 3, 4, 31, 3, 0, 9, 6, 1, 19, 6, 0, 9,
      3, 6, 33, 1, 7, 9, 1, 7, 6, 0, 0, 9, 4, 3, 31, 3, 7, 9, 6],
    [0, 6, 7, 0, 26, 2, 3, 19, 1, 5, 17, 5, 0, 39, 5, 0, 26, 7, 5, 36, 0, 5, 17, 0, 3, 34, 4,
      5, 17, 7, 6, 37, 1, 0, 26, 5, 5, 3, 2, 5, 17, 2, 1, 28, 3, 0, 26, 0],
    [0, 5, 2, 0, 25, 2, 2, 29, 5, 2, 18, 5, 6, 37, 6, 0, 25, 7, 4, 34, 1, 2, 18, 0, 2, 27, 7,
      2, 18, 7, 0, 30, 5, 0, 25, 5, 2, 6, 5, 2, 18, 2, 6, 19, 3, 0, 25, 0],
    [7, 14, 4, 5, 28, 0, 0, 4, 2, 6, 29, 0, 3, 10, 3, 5, 28, 5, 4, 47, 7, 6, 29, 5, 2, 7, 7, 6,
      29, 2, 7, 42, 4, 5, 28, 7, 0, 2, 5, 6, 29, 7, 1, 12, 6, 5, 28, 2],
    [2, 35, 0, 4, 24, 5, 4, 41, 2, 4, 10, 1, 4, 35, 0, 4, 24, 0, 2, 41, 2, 4, 10, 6, 2, 12, 7,
      4, 10, 3, 1, 25, 3, 4, 24, 2, 4, 12, 7, 4, 10, 4, 7, 25, 7, 4, 24, 7],
    [5, 13, 1, 4, 21, 4, 0, 17, 0, 4, 35, 6, 4, 26, 2, 4, 21, 3, 3, 32, 6, 4, 35, 1, 4, 16, 0,
      4, 35, 4, 2, 32, 5, 4, 21, 1, 2, 15, 4, 4, 35, 3, 7, 9, 4, 4, 21, 6],
    [0, 31, 0, 0, 11, 0, 3, 34, 2, 6, 11, 7, 2, 28, 0, 0, 11, 5, 5, 30, 6, 6, 11, 2, 4, 28, 0,
      6, 11, 5, 7, 34, 2, 0, 11, 7, 6, 31, 0, 6, 11, 0, 1, 30, 6, 0, 11, 2],
    [7, 9, 3, 1, 13, 0, 1, 35, 6, 0, 15, 1, 4, 17, 7, 1, 13, 5, 7, 48, 1, 0, 15, 6, 6, 18, 3,
      0, 15, 3, 2, 45, 5, 1, 13, 7, 0, 18, 7, 0, 15, 4, 1, 23, 2, 1, 13, 2],
    [5, 18, 2, 0, 10, 0, 0, 14, 2, 4, 20, 4, 0, 21, 4, 0, 10, 5, 6, 44, 5, 4, 20, 3, 6, 14, 2,
      4, 20, 6, 1, 18, 2, 0, 10, 7, 0, 44, 5, 4, 20, 1, 6, 21, 4, 0, 10, 2],
    [0, 3, 7, 2, 18, 4, 3, 38, 1, 0, 18, 1, 1, 28, 6, 2, 18, 3, 4, 33, 3, 0, 18, 6, 3, 28, 6,
      0, 18, 3, 1, 38, 1, 2, 18, 1, 2, 3, 7, 0, 18, 4, 6, 33, 3, 2, 18, 6],
    [0, 5, 5, 5, 17, 4, 6, 31, 1, 0, 17, 1, 0, 29, 0, 5, 17, 3, 4, 38, 3, 0, 17, 6, 5, 29, 0,
      0, 17, 3, 3, 31, 1, 5, 17, 1, 5, 5, 5, 0, 17, 4, 1, 38, 3, 5, 17, 6],
    [5, 3, 6, 6, 33, 1, 3, 32, 0, 0, 30, 6, 3, 34, 0, 6, 33, 6, 7, 15, 1, 0, 30, 1, 2, 23, 5,
      0, 30, 4, 5, 36, 4, 6, 33, 4, 1, 9, 5, 0, 30, 3, 3, 19, 5, 6, 33, 3],
    [4, 14, 1, 3, 29, 6, 0, 2, 2, 5, 19, 6, 2, 8, 4, 3, 29, 1, 7, 46, 0, 5, 19, 1, 7, 4, 7, 5,
      19, 4, 4, 41, 4, 3, 29, 3, 0, 7, 5, 5, 19, 3, 4, 20, 6, 3, 29, 4],
    [3, 4, 5, 1, 28, 3, 3, 44, 4, 6, 19, 7, 4, 2, 7, 1, 28, 4, 3, 12, 4, 6, 19, 2, 5, 8, 3, 6,
      19, 5, 3, 7, 2, 1, 28, 6, 7, 24, 1, 6, 19, 0, 7, 40, 7, 1, 28, 1],
    [3, 37, 5, 0, 27, 0, 4, 9, 1, 6, 33, 7, 4, 28, 7, 0, 27, 5, 7, 23, 1, 6, 33, 2, 6, 32, 4,
      6, 33, 5, 5, 39, 1, 0, 27, 7, 2, 15, 5, 6, 33, 0, 5, 6, 3, 0, 27, 2],
    [2, 21, 3, 1, 36, 1, 0, 28, 2, 1, 39, 5, 0, 21, 7, 1, 36, 6, 3, 3, 3, 1, 39, 0, 5, 33, 7,
      1, 39, 7, 7, 25, 5, 1, 36, 4, 0, 38, 5, 1, 39, 2, 4, 48, 2, 1, 36, 3],
    [1, 8, 6, 7, 45, 4, 6, 14, 3, 7, 32, 2, 1, 41, 3, 7, 45, 3, 0, 41, 1, 7, 32, 7, 0, 42, 1,
      7, 32, 0, 1, 44, 3, 7, 45, 1, 4, 24, 6, 7, 32, 5, 3, 10, 1, 7, 45, 6],
    [0, 13, 3, 6, 27, 1, 1, 29, 4, 6, 30, 0, 7, 13, 7, 6, 27, 6, 1, 5, 1, 6, 30, 5, 2, 38, 7,
      6, 30, 2, 2, 16, 1, 6, 27, 4, 0, 31, 5, 6, 30, 7, 7, 45, 0, 6, 27, 3],
    [1, 13, 2, 0, 37, 5, 3, 5, 4, 5, 38, 1, 1, 32, 7, 0, 37, 0, 3, 36, 3, 5, 38, 6, 0, 28, 5,
      5, 38, 3, 5, 23, 3, 0, 37, 2, 3, 27, 4, 5, 38, 4, 7, 17, 5, 0, 37, 7],
    [5, 17, 3, 4, 21, 0, 6, 23, 6, 0, 21, 2, 4, 9, 7, 4, 21, 5, 2, 45, 7, 0, 21, 7, 3, 17, 3,
      0, 21, 0, 3, 45, 1, 4, 21, 7, 0, 9, 7, 0, 21, 5, 2, 23, 6, 4, 21, 2],
    [2, 6, 1, 3, 31, 1, 7, 43, 7, 0, 39, 3, 2, 27, 3, 3, 31, 6, 5, 21, 2, 0, 39, 4, 7, 35, 5,
      0, 39, 1, 4, 34, 5, 3, 31, 4, 6, 18, 5, 0, 39, 6, 2, 29, 1, 3, 31, 3],
    [4, 13, 6, 5, 38, 0, 3, 30, 4, 0, 34, 4, 4, 32, 3, 5, 38, 5, 3, 3, 4, 0, 34, 3, 3, 29, 3,
      0, 34, 6, 2, 17, 1, 5, 38, 7, 3, 39, 4, 0, 34, 1, 0, 23, 7, 5, 38, 2],
    [5, 15, 2, 5, 34, 2, 0, 19, 2, 5, 37, 6, 0, 15, 6, 5, 34, 7, 6, 6, 4, 5, 37, 1, 7, 31, 7,
      5, 37, 4, 7, 26, 1, 5, 34, 5, 0, 33, 5, 5, 37, 3, 4, 45, 2, 5, 34, 0],
    [4, 37, 2, 0, 36, 7, 3, 43, 4, 3, 31, 5, 2, 5, 6, 0, 36, 2, 7, 21, 6, 3, 31, 0, 4, 18, 1,
      3, 31, 7, 2, 30, 1, 0, 36, 0, 1, 35, 7, 3, 31, 2, 4, 19, 7, 0, 36, 5],
    [5, 4, 4, 7, 47, 2, 0, 11, 2, 4, 46, 6, 0, 4, 4, 7, 47, 7, 5, 11, 2, 4, 46, 1, 2, 11, 2, 4,
      46, 4, 7, 4, 4, 7, 47, 5, 7, 11, 2, 4, 46, 3, 2, 4, 4, 7, 47, 0],
    [1, 27, 2, 6, 44, 0, 2, 2, 6, 6, 42, 6, 7, 37, 3, 6, 44, 5, 7, 46, 6, 6, 42, 1, 2, 7, 1, 6,
      42, 4, 1, 3, 5, 6, 44, 7, 5, 4, 3, 6, 42, 3, 0, 31, 6, 6, 44, 2],
    [3, 34, 3, 6, 41, 0, 6, 7, 6, 0, 44, 6, 5, 39, 2, 6, 41, 5, 7, 40, 1, 0, 44, 1, 6, 4, 1, 0,
      44, 4, 5, 5, 7, 6, 41, 7, 1, 2, 3, 0, 44, 3, 3, 33, 6, 6, 41, 2],
    [0, 8, 1, 4, 48, 6, 2, 14, 6, 4, 43, 5, 0, 42, 3, 4, 48, 1, 4, 44, 1, 4, 43, 0, 2, 44, 1,
      4, 43, 7, 6, 42, 3, 4, 48, 3, 4, 14, 6, 4, 43, 2, 6, 8, 1, 4, 48, 4],
    [5, 36, 2, 0, 42, 0, 3, 4, 6, 6, 41, 6, 5, 30, 7, 0, 42, 5, 7, 47, 3, 6, 41, 1, 3, 2, 1, 6,
      41, 4, 5, 6, 2, 0, 42, 7, 1, 7, 3, 6, 41, 3, 4, 38, 6, 0, 42, 2],
    [7, 20, 1, 7, 32, 4, 0, 44, 6, 0, 32, 6, 1, 12, 1, 7, 32, 3, 6, 42, 6, 0, 32, 1, 0, 20, 1,
      0, 32, 4, 1, 42, 6, 7, 32, 1, 6, 12, 1, 0, 32, 3, 7, 44, 6, 7, 32, 6],
    [6, 2, 4, 4, 40, 0, 7, 22, 3, 4, 47, 6, 4, 2, 4, 4, 40, 5, 3, 22, 7, 4, 47, 1, 4, 22, 7, 4,
      47, 4, 3, 2, 4, 4, 40, 7, 0, 22, 3, 4, 47, 3, 1, 2, 4, 4, 40, 2],
    [7, 7, 4, 4, 46, 0, 4, 11, 6, 7, 40, 1, 0, 7, 4, 4, 46, 5, 3, 11, 6, 7, 40, 6, 1, 11, 6, 7,
      40, 3, 2, 7, 4, 4, 46, 7, 6, 11, 6, 7, 40, 4, 5, 7, 4, 4, 46, 2],
    [6, 12, 3, 4, 43, 3, 4, 41, 6, 0, 43, 6, 0, 12, 3, 4, 43, 4, 2, 41, 6, 0, 43, 1, 4, 12, 3,
      0, 43, 4, 0, 41, 6, 4, 43, 6, 2, 12, 3, 0, 43, 3, 6, 41, 6, 4, 43, 1]]

@[expose] def decE (j b k e : ℕ) : ℕ := (decTab.getD j []).getD (6 * b + 3 * k + e) 0

@[expose] def DecOK (j : ℕ) : Prop :=
  ∀ b < 8, ∀ k < 2, decE j b k 0 < 8 ∧ decE j b k 1 < 49 ∧ decE j b k 2 < 8 ∧
    compL (compL (dL j) (telL b)) (gL k) =
      compL (compL (telL (decE j b k 0)) (dL (decE j b k 1))) (telL (decE j b k 2))

instance (j : ℕ) : Decidable (DecOK j) := by unfold DecOK; infer_instance

theorem dec_chk0 : ∀ j, 0 ≤ j → j < 7 → DecOK j := by decide +kernel

theorem dec_chk1 : ∀ j, 7 ≤ j → j < 14 → DecOK j := by decide +kernel

theorem dec_chk2 : ∀ j, 14 ≤ j → j < 21 → DecOK j := by decide +kernel

theorem dec_chk3 : ∀ j, 21 ≤ j → j < 28 → DecOK j := by decide +kernel

theorem dec_chk4 : ∀ j, 28 ≤ j → j < 35 → DecOK j := by decide +kernel

theorem dec_chk5 : ∀ j, 35 ≤ j → j < 42 → DecOK j := by decide +kernel

theorem dec_chk6 : ∀ j, 42 ≤ j → j < 49 → DecOK j := by decide +kernel

theorem dec_chk (j : ℕ) (hj : j < 49) : DecOK j := by
  by_cases h0 : j < 7
  · exact dec_chk0 j (by omega) h0
  by_cases h1 : j < 14
  · exact dec_chk1 j (by omega) h1
  by_cases h2 : j < 21
  · exact dec_chk2 j (by omega) h2
  by_cases h3 : j < 28
  · exact dec_chk3 j (by omega) h3
  by_cases h4 : j < 35
  · exact dec_chk4 j (by omega) h4
  by_cases h5 : j < 42
  · exact dec_chk5 j (by omega) h5
  exact dec_chk6 j (by omega) hj

@[expose] def wit0 : List (Fin 7 × List (ℕ × Bool)) :=
  [(0, []),
    (1, [(1, true)]),
    (2, [(1, false)]),
    (3, [(0, true), (1, false)]),
    (4, [(0, false), (0, false), (0, false)]),
    (5, [(0, false), (0, false)]),
    (6, [(0, false)])]

@[expose] def wit1 : List (Fin 7 × List (ℕ × Bool)) :=
  [(1, []),
    (2, [(0, true), (1, true), (0, false)]),
    (3, [(1, true), (0, true), (1, true)]),
    (4, [(1, false), (0, true), (1, true), (0, true), (1, true)]),
    (5, [(0, false), (0, false), (1, false)]),
    (6, [(1, false), (0, false), (1, false)])]

@[expose] def wit2 : List (Fin 7 × List (ℕ × Bool)) :=
  [(2, []),
    (3, [(1, false), (0, true)]),
    (4, [(1, false), (0, true), (1, false), (0, true)]),
    (5, [(0, false), (1, true), (0, false), (1, true)]),
    (6, [(0, false), (1, true)])]

@[expose] def wit3 : List (Fin 7 × List (ℕ × Bool)) :=
  [(3, []),
    (4, [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false)]),
    (5, [(0, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false)]),
    (6, [(0, false), (0, false), (0, false), (1, true), (0, false), (1, false), (0, false),
        (0, false), (0, false)])]

@[expose] def wit4 : List (Fin 7 × List (ℕ × Bool)) :=
  [(4, []),
    (5, [(0, true), (0, true), (1, false), (0, false), (0, false), (1, false), (0, true)]),
    (6, [(0, false), (1, true), (0, true), (0, true), (1, true), (0, false), (0, false)])]

theorem wit0_chk : ∀ x ∈ wit0,
    wordProd gen x.2 (0 : Fin 7) = x.1 := by
  decide +kernel

theorem wit1_chk : ∀ x ∈ wit1,
    wordProd gen x.2 (0 : Fin 7) = 0 ∧
    wordProd gen x.2 (1 : Fin 7) = x.1 := by
  decide +kernel

theorem wit2_chk : ∀ x ∈ wit2,
    wordProd gen x.2 (0 : Fin 7) = 0 ∧
    wordProd gen x.2 (1 : Fin 7) = 1 ∧
    wordProd gen x.2 (2 : Fin 7) = x.1 := by
  decide +kernel

theorem wit3_chk : ∀ x ∈ wit3,
    wordProd gen x.2 (0 : Fin 7) = 0 ∧
    wordProd gen x.2 (1 : Fin 7) = 1 ∧
    wordProd gen x.2 (2 : Fin 7) = 2 ∧
    wordProd gen x.2 (3 : Fin 7) = x.1 := by
  decide +kernel

theorem wit4_chk : ∀ x ∈ wit4,
    wordProd gen x.2 (0 : Fin 7) = 0 ∧
    wordProd gen x.2 (1 : Fin 7) = 1 ∧
    wordProd gen x.2 (2 : Fin 7) = 2 ∧
    wordProd gen x.2 (3 : Fin 7) = 3 ∧
    wordProd gen x.2 (4 : Fin 7) = x.1 := by
  decide +kernel

theorem wit_nodup :
    (wit0.map Prod.fst).Nodup ∧
    (wit1.map Prod.fst).Nodup ∧
    (wit2.map Prod.fst).Nodup ∧
    (wit3.map Prod.fst).Nodup ∧
    (wit4.map Prod.fst).Nodup := by
  decide +kernel

theorem wit_length :
    wit0.length = 7 ∧
    wit1.length = 6 ∧
    wit2.length = 5 ∧
    wit3.length = 4 ∧
    wit4.length = 3 := by
  decide +kernel

@[expose] def clsTab : List ℕ :=
  [0, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 4, 2, 2, 2, 3, 2, 3, 2, 2, 2, 3, 2, 3, 2, 2, 2, 6, 2, 2,
    2, 6, 2, 2, 3, 4, 7, 4, 3, 1, 2, 3, 4, 3, 2, 4, 1, 1]

@[expose] def good : List ℕ := [1, 40, 47, 48]

theorem cls_chk : ∀ j < 49, (j = 0 ∧ clsTab.getD j 0 = 0) ∨ (clsTab.getD j 0 = 1 ∧ j ∈ good) ∨
    (2 ≤ clsTab.getD j 0 ∧ clsTab.getD j 0 - 2 < 8 ∧
      powLst 7 (compL (dL j) (telL (clsTab.getD j 0 - 2))) 4 ≠ idL ∧
      powLst 7 (compL (dL j) (telL (clsTab.getD j 0 - 2))) 3 ≠ idL) := by
  decide +kernel

theorem good_lt_chk : ∀ j ∈ good, j < 49 := by decide +kernel

@[expose] def pairX (j j' : ℕ) : Finset (Finset (Fin 7)) :=
  if (j = 1 ∧ j' = 40) ∨ (j = 40 ∧ j' = 1) then
    {{4}, {5}, {6}}
  else if (j = 1 ∧ j' = 47) ∨ (j = 47 ∧ j' = 1) then
    {{4}, {5}, {6}}
  else if (j = 1 ∧ j' = 48) ∨ (j = 48 ∧ j' = 1) then
    {{6}}
  else if (j = 40 ∧ j' = 47) ∨ (j = 47 ∧ j' = 40) then
    {{4}, {5}, {6}}
  else if (j = 40 ∧ j' = 48) ∨ (j = 48 ∧ j' = 40) then
    {{0, 1, 4}, {0, 2, 6}, {0, 3, 5}, {1, 2, 5}, {1, 3, 6}, {2, 3, 4}, {4, 5, 6}}
  else if (j = 47 ∧ j' = 48) ∨ (j = 48 ∧ j' = 47) then
    {{0, 1, 5}, {0, 2, 6}, {0, 3, 4}, {1, 2, 4}, {1, 3, 6}, {2, 3, 5}, {4, 5, 6}}
  else ∅

theorem pair_chk : ∀ j ∈ good, ∀ j' ∈ good, j ≠ j' →
    (pairX j j').image (Finset.image (F6.lfun 7 rL)) = pairX j j' ∧
    (pairX j j').image (Finset.image (F6.lfun 7 fL)) = pairX j j' ∧
    (pairX j j').image (Finset.image (F6.lfun 7 (dL j))) = pairX j j' ∧
    (pairX j j').image (Finset.image (F6.lfun 7 (dL j'))) = pairX j j' ∧
    (pairX j j').image (Finset.image (F6.lfun 7 (gL 0))) ≠ pairX j j' := by
  decide +kernel

end CFSG.Quasithin.F6.A7Insp
