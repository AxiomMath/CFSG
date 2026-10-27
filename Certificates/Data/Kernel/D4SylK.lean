module

public import Certificates.Data.Kernel.D42K
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoSylowData

public section

namespace CFSG.KC.D4SylK

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two CFSG.KC.D42K

@[expose] def oneK : List (List Nat) := encM oneArr

@[expose] def letK (l : Nat) : List (List Nat) := encM (letterArr l)

@[expose] def wordK (w : List Nat) : List (List Nat) := w.foldr (fun l A => mulMK (letK l) A) oneK

@[expose] def aK : List (List Nat) := wordK wordA

@[expose] def bK : List (List Nat) := wordK wordB

@[expose] def bfsStepK (A B : List (List Nat)) (acc : List (List (List Nat))) (p : Nat × Bool) :
    List (List (List Nat)) :=
  acc ++ [mulMK (acc.getD p.1 oneK) (if p.2 then A else B)]

@[expose] def bfsK (A B : List (List Nat)) (par : List (Nat × Bool)) : List (List (List Nat)) :=
  par.foldl (bfsStepK A B) [oneK]

@[expose] def nxtTab : List (Nat × Nat) :=
  [(1, 2), (3, 4), (5, 6), (0, 7), (8, 9), (10, 11), (12, 0), (13, 14), (15, 16), (17, 1), (2, 18),
   (14, 19), (16, 20), (21, 22), (23, 3), (4, 24), (6, 25), (22, 26), (27, 28), (29, 5), (28, 30),
   (7, 31), (9, 32), (11, 33), (34, 35), (36, 8), (35, 37), (38, 39), (40, 10), (39, 41), (42, 12),
   (43, 44), (45, 13), (44, 46), (47, 48), (49, 15), (48, 50), (51, 17), (18, 52), (19, 53),
   (20, 54), (46, 55), (50, 56), (57, 58), (59, 21), (58, 60), (61, 23), (24, 62), (25, 63),
   (26, 64), (30, 65), (60, 66), (62, 67), (64, 27), (67, 68), (66, 29), (68, 69), (31, 70),
   (32, 71), (33, 72), (37, 73), (41, 74), (70, 75), (72, 34), (75, 76), (74, 36), (76, 77),
   (71, 38), (73, 40), (77, 42), (52, 78), (54, 43), (78, 79), (56, 45), (79, 80), (53, 47),
   (55, 49), (80, 51), (63, 57), (65, 59), (69, 61)]

@[expose] def edgeK (X : List (List (List Nat))) (par : List (Nat × Bool)) (G : List (List Nat))
    (i t : Nat) (g : Bool) : Bool :=
  decide (t < 81) && ((decide (0 < t) && decide (i < t) && par.getD (t - 1) (0, false) == (i, g)) ||
    X.getD t oneK == mulMK (X.getD i oneK) G)

@[expose] def enumCheckK (A B : List (List Nat)) (par : List (Nat × Bool)) (nxt : List (Nat × Nat)) :
    Bool :=
  let X := bfsK A B par
  X.length == 81 && decide X.Nodup &&
    (List.range 81).all fun i =>
      edgeK X par A i (nxt.getD i (0, 0)).1 true && edgeK X par B i (nxt.getD i (0, 0)).2 false

@[expose] def walkK (nxt : List (Nat × Nat)) (i : Nat) (w : List Bool) : Nat :=
  w.foldl (fun j g => if g then (nxt.getD j (0, 0)).1 else (nxt.getD j (0, 0)).2) i

@[expose] def witWords : List (List Bool) :=
  [[true, true, true, false, false, true, false], [true, true, false, false, true, false, true],
   [false, true, true, false, false, true, false], [true, true, false, false, true, false, false],
   [true, false, true, true, false, false, true, false],
   [true, true, false, false, true, false, true, false],
   [true, false, false, true, false, false, true, false, false]]

@[expose] def witCheckK (nxt : List (Nat × Nat)) (ws : List (List Bool)) : Bool :=
  let p := fun k => walkK nxt 0 (ws.getD k [])
  p 0 != p 1 && p 2 != p 3 && p 4 != p 5 && p 6 != 0

@[expose] def d4SylCheckK : Bool := enumCheckK aK bK bfsPar nxtTab && witCheckK nxtTab witWords

end CFSG.KC.D4SylK

end
