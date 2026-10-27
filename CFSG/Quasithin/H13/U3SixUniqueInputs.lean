module

public import CFSG.Quasithin.H13.U3SixRep

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.Quasithin Matrix

@[expose] def wordApply (w : List (Fin 5)) (c : ℕ) : ℕ :=
  w.foldr (fun i acc => vapp (u6c i) acc) c

@[expose] def kWords (b : ℕ) : List (List (Fin 5)) :=
  if b = 1 then [[3, 2], [0, 4, 0, 4]] else [[0]]

@[expose] def deriveSteps : List (ℕ × List (Fin 5) × ℕ) :=
  [(40, [1, 3, 4, 1], 1), (56, [3, 4], 1), (58, [0, 4, 2], 1), (42, [0, 4], 1), (62, [4, 4], 1),
    (22, [3, 4], 18), (44, [1, 4, 1], 1), (26, [1, 4, 3], 1), (18, [2, 3, 4], 18),
    (50, [2, 4, 4], 1), (59, [1, 1, 1, 4], 1), (41, [3, 3, 4], 1), (19, [1, 4], 1),
    (3, [1, 4, 3, 4], 1), (57, [0, 4], 18), (43, [3, 4, 3], 1), (17, [2, 3, 4, 3], 1),
    (36, [4, 0, 3, 4], 1), (53, [2, 4], 18), (15, [3], 18), (14, [], 1), (29, [], 18),
    (13, [2], 1), (39, [2], 18), (30, [4], 18), (28, [0, 0], 1), (37, [0, 1], 1),
    (55, [0, 3], 1), (38, [1, 1], 1), (52, [1, 3], 1), (7, [4, 0], 1), (11, [4, 1], 1),
    (21, [4, 3], 1), (31, [0, 0, 2], 1), (35, [0, 3, 4], 18), (47, [0, 4, 0], 1),
    (61, [0, 4, 3], 1), (49, [0, 4, 4], 1), (25, [2, 4, 3], 1), (54, [3, 4, 0], 1),
    (12, [1, 4], 18), (27, [3, 4, 3, 4], 1), (20, [0, 1, 3], 1), (51, [1, 3, 4], 1),
    (60, [0, 0, 0], 1), (6, [0, 1, 4], 1), (9, [0, 1, 1], 1), (46, [4, 0, 0], 1), (33, [0], 1),
    (45, [4, 3, 4], 1), (34, [3], 1), (23, [4, 2], 1), (48, [0, 3, 4], 1), (63, [1], 1),
    (5, [4], 1), (10, [0, 2], 1), (24, [1, 1, 1], 1)]

@[expose] def stepOK (D : List ℕ) (x : ℕ) (w : List (Fin 5)) (b : ℕ) : Bool :=
  let p := wordApply w 15
  let q := wordApply w b
  (b == 1 || b == 18) &&
    ((x == p && D.contains q && D.contains (p ^^^ q)) ||
      (x == q && D.contains p && D.contains (p ^^^ q)) ||
      (x == (p ^^^ q) && D.contains p && D.contains q))

@[expose] def deriveCheck : List ℕ → List (ℕ × List (Fin 5) × ℕ) → Bool
  | _, [] => true
  | D, (x, w, b) :: rest => stepOK D x w b && deriveCheck (x :: D) rest

section Unique

variable {V : Type*} [CommGroup V] [Finite V]

end Unique

end CFSG.Quasithin.H13.U3
