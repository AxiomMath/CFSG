module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelTable
public import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.StandardType.ZS.PrimModel

@[expose] def h3RootL : List (List ZAl) := [
    [qa 2 0, qa 0 0, qa 0 0, qa 0 0],
    [qa 0 1, qa 1 0, qa 1 0, qa 0 0],
    [qa 0 (-1), qa 1 0, qa 1 0, qa 0 0],
    [qa 0 1, qa (-1) 0, qa 1 0, qa 0 0],
    [qa 0 1, qa 1 0, qa (-1) 0, qa 0 0],
    [qa 1 (-1), qa 0 (-1), qa 0 (-1), qa 0 0],
    [qa 1 0, qa (-1) 1, qa 1 1, qa 0 0],
    [qa (-1) 1, qa 0 (-1), qa 0 (-1), qa 0 0],
    [qa 1 (-1), qa 0 1, qa 0 (-1), qa 0 0],
    [qa 1 (-1), qa 0 (-1), qa 0 1, qa 0 0],
    [qa (-1) 0, qa (-1) 1, qa 1 1, qa 0 0],
    [qa 1 0, qa 1 (-1), qa 1 1, qa 0 0],
    [qa 1 0, qa (-1) 1, qa (-1) (-1), qa 0 0],
    [qa 0 0, qa 0 0, qa 0 (-2), qa 0 0],
    [qa 0 0, qa (-2) 0, qa 0 0, qa 0 0]]

@[expose] def h3CorootL : List (List ZAl) := [
    [qa 2 0, qa 0 0, qa 0 0, qa 0 0],
    [qa 0 1, qa 1 0, qa 2 (-1), qa 0 0],
    [qa 0 (-1), qa 1 0, qa 2 (-1), qa 0 0],
    [qa 0 1, qa (-1) 0, qa 2 (-1), qa 0 0],
    [qa 0 1, qa 1 0, qa (-2) 1, qa 0 0],
    [qa 1 (-1), qa 0 (-1), qa 1 (-1), qa 0 0],
    [qa 1 0, qa (-1) 1, qa 1 0, qa 0 0],
    [qa (-1) 1, qa 0 (-1), qa 1 (-1), qa 0 0],
    [qa 1 (-1), qa 0 1, qa 1 (-1), qa 0 0],
    [qa 1 (-1), qa 0 (-1), qa (-1) 1, qa 0 0],
    [qa (-1) 0, qa (-1) 1, qa 1 0, qa 0 0],
    [qa 1 0, qa 1 (-1), qa 1 0, qa 0 0],
    [qa 1 0, qa (-1) 1, qa (-1) 0, qa 0 0],
    [qa 0 0, qa 0 0, qa 2 (-2), qa 0 0],
    [qa 0 0, qa (-2) 0, qa 0 0, qa 0 0]]

@[expose] def h3ConjL : List (List (Fin 15)) := [
    [0, 2, 1, 4, 3, 7, 10, 5, 9, 8, 6, 12, 11, 13, 14],
    [0, 3, 4, 1, 2, 8, 11, 9, 5, 7, 12, 6, 10, 13, 14],
    [0, 4, 3, 2, 1, 9, 12, 8, 7, 5, 11, 10, 6, 13, 14],
    [1, 0, 5, 6, 4, 2, 3, 7, 13, 12, 14, 11, 9, 8, 10]]

@[expose] def h3SignL : List (List Bool) := [
    [false, true, true, false, false, true, true, true, false, false, true, false, false, true,
    true],
    [true, true, false, true, false, true, true, false, true, false, false, true, false, true,
    false],
    [true, true, false, false, true, true, true, false, false, true, false, false, true, false,
    true],
    [true, true, true, true, true, true, true, false, true, false, true, true, false, true, true]]

@[expose] def h3WordL : List (List (Fin 4)) := [
    [],
    [3],
    [0, 3],
    [1, 3],
    [2, 3],
    [3, 0, 3],
    [3, 1, 3],
    [0, 3, 0, 3],
    [1, 3, 0, 3],
    [2, 3, 0, 3],
    [0, 3, 1, 3],
    [1, 3, 1, 3],
    [2, 3, 1, 3],
    [3, 1, 3, 0, 3],
    [3, 0, 3, 1, 3]]

@[expose] def h3ClsL : List (Fin 4) :=
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def h3GenL : List (Fin 15) := [0, 14, 13, 7]

@[expose] def h3Tab : ReflTable ZAl 4 4 15 where
  root j i := (h3RootL.getD j []).getD i 0
  coroot j i := (h3CorootL.getD j []).getD i 0
  gen k := h3GenL.getD k 0
  conj k j := (h3ConjL.getD k []).getD j 0
  sign k j := (h3SignL.getD k []).getD j true
  word j := h3WordL.getD j []
  cls j := h3ClsL.getD j 0

@[expose] def h3G : Fin 4 → Matrix (Fin 4) (Fin 4) ZAl := ![
    !![qa (-2) 0, qa 0 0, qa 0 0, qa 0 0; qa 0 0, qa 2 0, qa 0 0, qa 0 0; qa 0 0, qa 0 0, qa 2 0,
    qa 0 0; qa 0 0, qa 0 0, qa 0 0, qa 2 0],
    !![qa 2 0, qa 0 0, qa 0 0, qa 0 0; qa 0 0, qa (-2) 0, qa 0 0, qa 0 0; qa 0 0, qa 0 0, qa 2 0,
    qa 0 0; qa 0 0, qa 0 0, qa 0 0, qa 2 0],
    !![qa 2 0, qa 0 0, qa 0 0, qa 0 0; qa 0 0, qa 2 0, qa 0 0, qa 0 0; qa 0 0, qa 0 0, qa (-2) 0,
    qa 0 0; qa 0 0, qa 0 0, qa 0 0, qa 2 0],
    !![qa 0 1, qa 1 0, qa 2 (-1), qa 0 0; qa 1 0, qa 1 (-1), qa (-1) 0, qa 0 0; qa 1 0, qa (-1)
    (-1), qa 1 0, qa 0 0; qa 0 0, qa 0 0, qa 0 0, qa 2 0]]

@[expose] def h3WitL : List (Fin 15) :=
    [14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def h3Wit (j : Fin 15) : Fin 15 := h3WitL.getD j 0

@[expose] def h3PtL : List (List ZAl) := [
    [qa 2 0, qa 0 0, qa 0 0, qa 0 0],
    [qa (-2) 0, qa 0 0, qa 0 0, qa 0 0],
    [qa 0 1, qa 1 0, qa 1 0, qa 0 0],
    [qa 0 (-1), qa (-1) 0, qa (-1) 0, qa 0 0],
    [qa 0 (-1), qa 1 0, qa 1 0, qa 0 0],
    [qa 0 1, qa (-1) 0, qa (-1) 0, qa 0 0],
    [qa 0 1, qa (-1) 0, qa 1 0, qa 0 0],
    [qa 0 (-1), qa 1 0, qa (-1) 0, qa 0 0],
    [qa 0 1, qa 1 0, qa (-1) 0, qa 0 0],
    [qa 0 (-1), qa (-1) 0, qa 1 0, qa 0 0],
    [qa 1 (-1), qa 0 (-1), qa 0 (-1), qa 0 0],
    [qa (-1) 1, qa 0 1, qa 0 1, qa 0 0],
    [qa 1 0, qa (-1) 1, qa 1 1, qa 0 0],
    [qa (-1) 0, qa 1 (-1), qa (-1) (-1), qa 0 0],
    [qa (-1) 1, qa 0 (-1), qa 0 (-1), qa 0 0],
    [qa 1 (-1), qa 0 1, qa 0 1, qa 0 0],
    [qa 1 (-1), qa 0 1, qa 0 (-1), qa 0 0],
    [qa (-1) 1, qa 0 (-1), qa 0 1, qa 0 0],
    [qa 1 (-1), qa 0 (-1), qa 0 1, qa 0 0],
    [qa (-1) 1, qa 0 1, qa 0 (-1), qa 0 0],
    [qa (-1) 0, qa (-1) 1, qa 1 1, qa 0 0],
    [qa 1 0, qa 1 (-1), qa (-1) (-1), qa 0 0],
    [qa 1 0, qa 1 (-1), qa 1 1, qa 0 0],
    [qa (-1) 0, qa (-1) 1, qa (-1) (-1), qa 0 0],
    [qa 1 0, qa (-1) 1, qa (-1) (-1), qa 0 0],
    [qa (-1) 0, qa 1 (-1), qa 1 1, qa 0 0],
    [qa 0 0, qa 0 0, qa 0 (-2), qa 0 0],
    [qa 0 0, qa 0 0, qa 0 2, qa 0 0],
    [qa 0 0, qa (-2) 0, qa 0 0, qa 0 0],
    [qa 0 0, qa 2 0, qa 0 0, qa 0 0],
    [qa 0 0, qa 0 0, qa 0 0, qa 1 0]]

@[expose] def h3PiL : List (List (Fin 31)) := [
    [1, 0, 4, 5, 2, 3, 9, 8, 7, 6, 14, 15, 20, 21, 10, 11, 19, 18, 17, 16, 12, 13, 25, 24, 23,
    22, 26, 27, 28, 29, 30],
    [0, 1, 6, 7, 9, 8, 2, 3, 5, 4, 16, 17, 22, 23, 19, 18, 10, 11, 15, 14, 25, 24, 12, 13, 21,
    20, 26, 27, 29, 28, 30],
    [0, 1, 8, 9, 7, 6, 5, 4, 2, 3, 18, 19, 24, 25, 17, 16, 15, 14, 10, 11, 23, 22, 21, 20, 12,
    13, 27, 26, 28, 29, 30],
    [2, 3, 0, 1, 10, 11, 12, 13, 8, 9, 4, 5, 6, 7, 15, 14, 26, 27, 25, 24, 28, 29, 22, 23, 19,
    18, 16, 17, 20, 21, 30]]

@[expose] def h3OrbL : List (Fin 4 → Fin 31) := [
    ![0, 2, 6, 30], ![1, 4, 9, 30], ![0, 6, 2, 30], ![0, 8, 5, 30], ![2, 0, 12, 30], ![1, 9, 4,
    30], ![1, 7, 3, 30], ![3, 10, 9, 30], ![0, 5, 8, 30], ![2, 12, 0, 30], ![2, 8, 11, 30], ![4,
    1, 20, 30], ![6, 0, 22, 30], ![8, 0, 24, 30], ![1, 3, 7, 30], ![3, 9, 10, 30], ![3, 13, 1,
    30], ![5, 14, 6, 30], ![7, 16, 4, 30], ![9, 18, 3, 30], ![2, 11, 8, 30], ![4, 20, 1, 30],
    ![6, 22, 0, 30], ![8, 24, 0, 30], ![4, 7, 15, 30], ![6, 5, 17, 30], ![8, 2, 19, 30], ![9, 1,
    25, 30], ![7, 1, 23, 30], ![10, 3, 28, 30], ![5, 0, 21, 30], ![12, 2, 22, 30], ![3, 1, 13,
    30], ![5, 6, 14, 30], ![7, 4, 16, 30], ![9, 3, 18, 30], ![5, 21, 0, 30], ![7, 23, 1, 30],
    ![9, 25, 1, 30], ![8, 19, 2, 30], ![6, 17, 5, 30], ![11, 15, 12, 30], ![4, 15, 7, 30], ![13,
    26, 10, 30], ![10, 28, 3, 30], ![12, 22, 2, 30], ![10, 13, 14, 30], ![12, 11, 27, 30], ![13,
    3, 23, 30], ![14, 5, 28, 30], ![16, 7, 29, 30], ![18, 9, 28, 30], ![11, 2, 29, 30], ![20, 4,
    25, 30], ![22, 6, 12, 30], ![24, 8, 21, 30], ![11, 12, 15, 30], ![13, 10, 26, 30], ![11, 29,
    2, 30], ![13, 23, 3, 30], ![12, 27, 11, 30], ![15, 11, 20, 30], ![17, 18, 22, 30], ![19, 16,
    24, 30], ![10, 14, 13, 30], ![21, 26, 14, 30], ![23, 26, 16, 30], ![25, 27, 18, 30], ![14,
    28, 5, 30], ![16, 29, 7, 30], ![18, 28, 9, 30], ![20, 25, 4, 30], ![22, 12, 6, 30], ![24, 21,
    8, 30], ![14, 21, 10, 30], ![16, 23, 19, 30], ![18, 25, 17, 30], ![20, 15, 27, 30], ![22, 17,
    27, 30], ![24, 19, 26, 30], ![21, 5, 24, 30], ![23, 7, 13, 30], ![25, 9, 20, 30], ![19, 8,
    29, 30], ![17, 6, 28, 30], ![15, 4, 29, 30], ![26, 13, 21, 30], ![28, 10, 18, 30], ![15, 20,
    11, 30], ![17, 22, 18, 30], ![19, 24, 16, 30], ![21, 14, 26, 30], ![23, 16, 26, 30], ![25,
    18, 27, 30], ![15, 29, 4, 30], ![17, 28, 6, 30], ![19, 29, 8, 30], ![21, 24, 5, 30], ![23,
    13, 7, 30], ![25, 20, 9, 30], ![20, 27, 15, 30], ![22, 27, 17, 30], ![24, 26, 19, 30], ![18,
    17, 25, 30], ![16, 19, 23, 30], ![14, 10, 21, 30], ![27, 25, 22, 30], ![29, 16, 15, 30],
    ![26, 21, 13, 30], ![28, 18, 10, 30], ![26, 23, 24, 30], ![28, 14, 17, 30], ![29, 11, 19,
    30], ![27, 12, 20, 30], ![27, 22, 25, 30], ![29, 15, 16, 30], ![27, 20, 12, 30], ![29, 19,
    11, 30], ![28, 17, 14, 30], ![26, 24, 23, 30]]

@[expose] def h3NxtL : List (List (Fin 120)) := [
    [1, 0, 5, 6, 11, 2, 3, 17, 14, 21, 24, 4, 27, 28, 8, 33, 36, 7, 39, 40, 42, 9, 38, 37, 10,
    35, 34, 12, 13, 49, 32, 53, 30, 15, 26, 25, 16, 23, 22, 18, 19, 61, 20, 65, 68, 71, 74, 77,
    80, 29, 83, 84, 85, 31, 82, 81, 88, 91, 94, 97, 100, 41, 103, 104, 105, 43, 102, 101, 44, 96,
    95, 45, 99, 98, 46, 90, 89, 47, 93, 92, 48, 55, 54, 50, 51, 52, 108, 111, 56, 76, 75, 57, 79,
    78, 58, 70, 69, 59, 73, 72, 60, 67, 66, 62, 63, 64, 114, 117, 86, 118, 119, 87, 115, 116,
    106, 112, 113, 107, 109, 110],
    [2, 5, 0, 8, 12, 1, 14, 18, 3, 22, 25, 27, 4, 30, 6, 34, 37, 39, 7, 42, 40, 38, 9, 36, 35,
    10, 33, 11, 32, 50, 13, 54, 28, 26, 15, 24, 23, 16, 21, 17, 20, 62, 19, 66, 69, 72, 75, 78,
    81, 83, 29, 85, 84, 82, 31, 80, 89, 92, 95, 98, 101, 103, 41, 105, 104, 102, 43, 100, 96, 44,
    94, 99, 45, 97, 90, 46, 88, 93, 47, 91, 55, 48, 53, 49, 52, 51, 110, 107, 76, 56, 74, 79, 57,
    77, 70, 58, 68, 73, 59, 71, 67, 60, 65, 61, 64, 63, 116, 87, 119, 115, 86, 117, 118, 114,
    113, 109, 106, 111, 112, 108],
    [3, 6, 8, 0, 13, 14, 1, 19, 2, 23, 26, 28, 30, 4, 5, 35, 38, 40, 42, 7, 39, 37, 36, 9, 34,
    33, 10, 32, 11, 51, 12, 55, 27, 25, 24, 15, 22, 21, 16, 20, 17, 63, 18, 67, 70, 73, 76, 79,
    82, 84, 85, 29, 83, 81, 80, 31, 90, 93, 96, 99, 102, 104, 105, 41, 103, 101, 100, 43, 95, 94,
    44, 98, 97, 45, 89, 88, 46, 92, 91, 47, 54, 53, 48, 52, 49, 50, 106, 109, 75, 74, 56, 78, 77,
    57, 69, 68, 58, 72, 71, 59, 66, 65, 60, 64, 61, 62, 86, 115, 114, 87, 116, 118, 117, 119,
    108, 107, 110, 112, 111, 113],
    [4, 7, 9, 10, 0, 15, 16, 1, 20, 2, 3, 29, 31, 26, 32, 5, 6, 41, 43, 38, 8, 44, 45, 39, 46,
    47, 13, 35, 48, 11, 52, 12, 14, 56, 57, 27, 58, 59, 19, 23, 60, 17, 64, 18, 21, 22, 24, 25,
    28, 61, 86, 82, 30, 87, 72, 83, 33, 34, 36, 37, 40, 49, 106, 102, 42, 107, 92, 103, 88, 108,
    99, 109, 54, 96, 94, 110, 93, 111, 101, 90, 112, 98, 51, 55, 113, 105, 50, 53, 68, 114, 79,
    115, 66, 76, 74, 116, 73, 117, 81, 70, 118, 78, 63, 67, 119, 85, 62, 65, 69, 71, 75, 77, 80,
    84, 89, 91, 95, 97, 100, 104]]

@[expose] def h3PredL : List (Fin 120) :=
    [0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 3, 4, 4, 4, 5, 5, 6, 7, 7, 7, 8, 9, 9, 9, 10, 10, 10, 11, 11,
    11, 12, 12, 14, 15, 15, 15, 16, 16, 16, 17, 17, 17, 18, 18, 21, 22, 24, 25, 28, 29, 29, 29,
    30, 31, 31, 31, 33, 34, 36, 37, 40, 41, 41, 41, 42, 43, 43, 43, 44, 44, 44, 45, 45, 45, 46,
    46, 46, 47, 47, 47, 48, 48, 48, 49, 49, 50, 50, 53, 56, 56, 56, 57, 57, 57, 58, 58, 58, 59,
    59, 59, 60, 60, 60, 61, 61, 62, 62, 65, 69, 71, 75, 77, 80, 84, 89, 91, 95, 97, 100, 104]

@[expose] def h3PkL : List (Fin 4) :=
    [0, 0, 1, 2, 3, 1, 2, 3, 2, 3, 3, 0, 1, 2, 2, 3, 3, 0, 1, 2, 3, 0, 1, 2, 0, 1, 2, 1, 2, 3, 2,
    3, 3, 0, 1, 2, 0, 1, 2, 1, 2, 3, 2, 3, 3, 3, 3, 3, 3, 0, 1, 2, 3, 0, 1, 2, 3, 3, 3, 3, 3, 0,
    1, 2, 3, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 2, 2, 3, 3, 0, 1, 2, 0, 1,
    2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]

@[expose] def h3SpanL : List (List ZAl) := [
    [qa 1 0, qa 0 0, qa 0 0, qa 0 0],
    [qa 0 0, qa 1 0, qa (-1) 0, qa 0 0],
    [qa 0 (-1), qa 1 0, qa 1 0, qa 0 0],
    [qa 0 0, qa 0 0, qa 0 0, qa 2 0]]

@[expose] def h3Pt (x : Fin 31) : Fin 4 → ZAl := fun i => (h3PtL.getD x []).getD i 0
@[expose] def h3Pi (k : Fin 4) (x : Fin 31) : Fin 31 := (h3PiL.getD k []).getD x 0
@[expose] def h3Orb (i : Fin 120) : Fin 4 → Fin 31 := h3OrbL.getD i 0
@[expose] def h3Nxt (k : Fin 4) (i : Fin 120) : Fin 120 := (h3NxtL.getD k []).getD i 0
@[expose] def h3Pred (i : Fin 120) : Fin 120 := h3PredL.getD i 0
@[expose] def h3Pk (i : Fin 120) : Fin 4 := h3PkL.getD i 0
@[expose] def h3Span (i l : Fin 4) : ZAl := (h3SpanL.getD i []).getD l 0

@[expose] def h3RcL : List (List (Fin 15)) := [
    [0, 2, 1, 4, 3, 7, 10, 5, 9, 8, 6, 12, 11, 13, 14],
    [5, 1, 7, 14, 6, 0, 4, 2, 8, 11, 10, 9, 13, 12, 3],
    [7, 5, 2, 10, 14, 1, 6, 0, 12, 9, 3, 13, 8, 11, 4],
    [8, 14, 11, 3, 9, 5, 7, 6, 0, 4, 13, 2, 12, 10, 1],
    [9, 12, 14, 8, 4, 10, 13, 7, 3, 0, 5, 11, 1, 6, 2],
    [2, 7, 0, 3, 10, 5, 14, 1, 11, 13, 4, 8, 12, 9, 6],
    [10, 13, 2, 7, 12, 11, 6, 3, 14, 9, 0, 5, 4, 1, 8],
    [1, 0, 5, 6, 4, 2, 3, 7, 13, 12, 14, 11, 9, 8, 10],
    [4, 1, 12, 9, 0, 6, 5, 13, 8, 3, 10, 14, 2, 7, 11],
    [3, 11, 2, 0, 8, 13, 6, 10, 4, 9, 7, 1, 14, 5, 12],
    [6, 1, 13, 11, 5, 4, 0, 12, 8, 14, 10, 3, 7, 2, 9],
    [12, 9, 10, 13, 4, 14, 8, 7, 6, 1, 2, 11, 0, 3, 5],
    [11, 6, 8, 3, 13, 5, 1, 14, 2, 10, 9, 0, 12, 4, 7],
    [0, 4, 3, 2, 1, 9, 12, 8, 7, 5, 11, 10, 6, 13, 14],
    [0, 3, 4, 1, 2, 8, 11, 9, 5, 7, 12, 6, 10, 13, 14]]

@[expose] def h3RsL : List (List Bool) := [
    [false, true, true, false, false, true, true, true, false, false, true, false, false, true,
    true],
    [true, false, false, true, false, true, false, false, true, true, true, true, true, true,
    true],
    [false, false, false, true, false, false, true, false, true, true, true, false, true, false,
    false],
    [true, false, true, false, false, true, false, false, true, false, false, true, true, false,
    false],
    [true, false, false, false, false, false, false, true, false, true, false, true, false,
    false, false],
    [false, true, false, true, false, false, true, true, false, false, false, false, true, false,
    true],
    [false, true, true, true, true, true, false, true, false, true, false, true, true, true,
    false],
    [true, true, true, true, true, true, true, false, true, false, true, true, false, true, true],
    [true, true, false, false, true, false, false, true, false, false, true, false, false, true,
    false],
    [true, true, true, true, false, true, true, false, false, false, false, true, true, true,
    true],
    [true, true, true, true, false, false, true, false, true, true, false, true, false, true,
    true],
    [true, false, true, true, true, true, true, true, true, false, true, false, true, true, true],
    [true, true, true, true, false, true, true, true, true, false, false, true, false, false,
    true],
    [true, true, false, false, true, true, true, false, false, true, false, false, true, false,
    true],
    [true, true, false, true, false, true, true, false, true, false, false, true, false, true,
    false]]

@[expose] def h3Rc (i k : Fin 15) : Fin 15 := (h3RcL.getD i []).getD k 0
@[expose] def h3Rs (i k : Fin 15) : Bool := (h3RsL.getD i []).getD k true

@[expose] def h3OrdL : List ℕ := [1, 5, 5, 5, 5, 5, 3, 5, 5, 5, 3, 3, 3, 2, 2]

@[expose] def h3Ord (j : Fin 15) : ℕ := h3OrdL.getD j 1

@[expose] def h3A5L : List (List (List Bool)) := [
    [[], [], [], [], [], [], [], [], [], [], [], [], [], [], []],
    [[], [false, true, false, true], [false, true, false], [false], [false, true], [false],
    [false, true, false], [false, true], [false, true, false, true], [false, true, false],
    [false, true, false, true], [false, true], [false], [], []],
    [[], [false, true, false], [false, true, false, true], [false, true], [false], [false, true],
    [false, true, false, true], [false], [false, true, false], [false, true, false, true],
    [false, true, false], [false], [false, true], [], []],
    [[], [false], [false, true], [false, true, false, true], [false, true, false], [false, true,
    false, true], [false, true], [false, true, false], [false], [false, true], [false], [false,
    true, false], [false, true, false, true], [], []],
    [[], [false, true], [false], [false, true, false], [false, true, false, true], [false, true,
    false], [false], [false, true, false, true], [false, true], [false], [false, true], [false,
    true, false, true], [false, true, false], [], []],
    [[], [false, true], [false], [false, true, false, true], [false, true, false], [false, true,
    false, true], [false], [false, true, false], [false, true], [false], [false, true], [false,
    true, false], [false, true, false, true], [], []],
    [[], [], [], [], [], [], [], [], [], [], [], [], [], [], []],
    [[], [false], [false, true], [false, true, false], [false, true, false, true], [false, true,
    false], [false, true], [false, true, false, true], [false], [false, true], [false], [false,
    true, false, true], [false, true, false], [], []],
    [[], [false, true, false, true], [false, true, false], [false, true], [false], [false, true],
    [false, true, false], [false], [false, true, false, true], [false, true, false], [false,
    true, false, true], [false], [false, true], [], []],
    [[], [false, true, false], [false, true, false, true], [false], [false, true], [false],
    [false, true, false, true], [false, true], [false, true, false], [false, true, false, true],
    [false, true, false], [false, true], [false], [], []],
    [[], [], [], [], [], [], [], [], [], [], [], [], [], [], []],
    [[], [], [], [], [], [], [], [], [], [], [], [], [], [], []],
    [[], [], [], [], [], [], [], [], [], [], [], [], [], [], []],
    [[], [], [], [], [], [], [], [], [], [], [], [], [], [], []],
    [[], [], [], [], [], [], [], [], [], [], [], [], [], [], []]]

@[expose] def h3A5 (j k : Fin 15) : List Bool := (h3A5L.getD j []).getD k []

@[expose] def h3Ell : Fin 4 → ZAl := ![qa 0 0, qa 1 0, qa (-1) 0, qa 0 0]

@[expose] def h3PairWL : List (List Bool) := [
    [],
    [false],
    [true, false],
    [],
    [],
    [true],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    []]

@[expose] def h3PairBL : List Bool :=
    [true, true, true, true, true, false, true, false, true, true, true, true, true, true, true]

@[expose] def h3PairW (j : Fin 15) : List Bool := h3PairWL.getD j []
@[expose] def h3PairB (j : Fin 15) : Bool := h3PairBL.getD j true

@[expose] def h3D : Fin 4 → ZAl := ![qa 1 0, qa 1 0, qa 2 (-1), qa 1 0]

@[expose] def h3A5Img (j k : Fin 15) : Fin 15 :=
  (h3A5 j k).foldr (fun x k => h3Rc (if x then 0 else j) k) k

@[expose] def h3PairImg (j : Fin 15) : Fin 15 :=
  (h3PairW j).foldr (fun x k => h3Rc (if x then 0 else 7) k) (if h3PairB j then 0 else 7)

@[expose] def h3UnitIdx : Fin 3 → Fin 15 := ![0, 14, 13]

@[expose] def h3UnitCoef : Fin 3 → ZAl := ![qa 1 0, qa (-1) 0, qa 1 (-1)]

theorem h3Tab_valid : h3Tab.Valid GoodAl :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

theorem h3Tab_gen : ∀ k : Fin 4,
    reflZ (h3Tab.root (h3Tab.gen k)) (h3Tab.coroot (h3Tab.gen k)) = h3G k := by
  decide +kernel

theorem h3Tab_form : ∀ k : Fin 4,
    (∑ i, h3D i * h3Tab.root (h3Tab.gen k) i ^ 2) • h3Tab.coroot (h3Tab.gen k) =
      (4 : ZAl) • fun i => h3D i * h3Tab.root (h3Tab.gen k) i := by
  decide +kernel

theorem h3D_good : ∀ i, GoodAl (h3D i) := by
  decide +kernel

theorem h3Tab_wit : ∀ j, (∀ i ∉ ({0, 1} : Finset (Fin 4)), h3Tab.root j i = 0) →
    (∀ i ∉ ({0, 1} : Finset (Fin 4)), h3Tab.root (h3Wit j) i = 0) ∧
      dotProduct (h3Tab.coroot j) (h3Tab.root (h3Wit j)) = 0 ∧
      h3Tab.cls (h3Wit j) = h3Tab.cls 0 := by
  decide +kernel

theorem h3Tab_diag : reflZ (h3Tab.root 0) (h3Tab.coroot 0) = diagZ 0 ∧
    reflZ (h3Tab.root 14) (h3Tab.coroot 14) = diagZ 1 ∧
    reflZ (h3Tab.root 13) (h3Tab.coroot 13) = diagZ 2 := by
  decide +kernel

theorem h3_pt_act : ∀ (k : Fin 4) (x : Fin 31),
    (2 : ZAl) • h3Pt x - dotProduct (h3Tab.coroot (h3Tab.gen k)) (h3Pt x) •
      h3Tab.root (h3Tab.gen k) = (2 : ZAl) • h3Pt (h3Pi k x) := by
  decide +kernel

theorem h3_pt_ne : ∀ x y : Fin 31, x ≠ y → ∃ l, GoodAl (h3Pt x l - h3Pt y l) := by
  decide +kernel

theorem h3_orb_nxt : ∀ (k : Fin 4) (i : Fin 120),
    h3Orb (h3Nxt k i) = fun l => h3Pi k (h3Orb i l) := by
  decide +kernel

theorem h3_orb_pred : ∀ i : Fin 120, i = 0 ∨
    (h3Pred i < i ∧ h3Orb i = fun l => h3Pi (h3Pk i) (h3Orb (h3Pred i) l)) := by
  decide +kernel

theorem h3_orb_key : CFSG.Decide.bitsetNodup ((List.ofFn h3Orb).map fun t =>
    CFSG.Decide.finFunKey fun l : Fin 3 => t l.castSucc) = true := by
  decide +kernel

theorem h3_span : ∀ i : Fin 4,
    ∑ l, h3Span i l • h3Pt (h3Orb 0 l) = (2 : ZAl) ^ 1 • Pi.single i 1 := by
  decide +kernel

theorem h3_rc : ∀ a k : Fin 15, h3Tab.ConjRel a k (h3Rc a k) (h3Rs a k) := by
  decide +kernel

theorem h3_ord : ∀ j : Fin 15,
    (reflZ (h3Tab.root 0) (h3Tab.coroot 0) * reflZ (h3Tab.root j) (h3Tab.coroot j)) ^ h3Ord j =
      (4 : ZAl) ^ h3Ord j • (1 : Matrix (Fin 4) (Fin 4) ZAl) := by
  decide +kernel

theorem h3_ord_cases : ∀ j : Fin 15, h3Ord j = 5 ∨ (0 < h3Ord j ∧ h3Ord j ≤ 3) := by
  decide +kernel

theorem h3_ne_one : GoodAl ((reflZ (h3Tab.root 0) (h3Tab.coroot 0) *
    reflZ (h3Tab.root 1) (h3Tab.coroot 1) - (4 : ZAl) • (1 : Matrix (Fin 4) (Fin 4) ZAl)) 1 1) := by
  decide +kernel

theorem h3_a5 : ∀ j k : Fin 15, h3Ord j = 5 → h3A5Img j k = 0 ∨
    (dotProduct (h3Tab.coroot 0) (h3Tab.root (h3A5Img j k)) = 0 ∧
      dotProduct (h3Tab.coroot (h3A5Img j k)) (h3Tab.root 0) = 0) := by
  decide +kernel

theorem h3_ell : dotProduct h3Ell (h3Tab.root 0) = 0 ∧ dotProduct h3Ell (h3Tab.root 7) = 0 ∧
    ∀ j, dotProduct h3Ell (h3Tab.root j) = 0 ∨ GoodAl (dotProduct h3Ell (h3Tab.root j)) := by
  decide +kernel

theorem h3_pair : ∀ j : Fin 15, dotProduct h3Ell (h3Tab.root j) = 0 → h3PairImg j = j := by
  decide +kernel

theorem h3_hub : ∀ i : Fin 3,
    GoodAl (h3Tab.root 7 i.castSucc) ∧ GoodAl (h3Tab.coroot 7 i.castSucc) := by
  decide +kernel

theorem h3_last : ∀ j : Fin 15, h3Tab.root j 3 = 0 ∧ h3Tab.coroot j 3 = 0 := by
  decide +kernel

theorem h3_unit : ∀ i : Fin 3,
    h3UnitCoef i • h3Tab.root (h3UnitIdx i) = (2 : ZAl) ^ 1 • Pi.single i.castSucc 1 := by
  decide +kernel

end CFSG.StandardType.ZS.PrimModel

end
