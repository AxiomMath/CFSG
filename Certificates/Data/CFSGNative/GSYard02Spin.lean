module

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02.SpinNative

set_option compiler.extract_closed false

abbrev Mat (N : Nat) : Type := Vector (Vector Rat N) N

@[expose] def ent {N : Nat} (A : Mat N) (i j : Fin N) : Rat := (A.get i).get j

@[expose] def ofF {N : Nat} (f : Fin N → Fin N → Rat) : Mat N :=
  Vector.ofFn fun i => Vector.ofFn fun j => f i j

@[expose] def oneM (N : Nat) : Mat N := ofF fun i j => if i = j then 1 else 0

@[expose] def zeroM (N : Nat) : Mat N := ofF fun _ _ => 0

@[expose] def addM {N : Nat} (A B : Mat N) : Mat N := ofF fun i j => ent A i j + ent B i j

@[expose] def subM {N : Nat} (A B : Mat N) : Mat N := ofF fun i j => ent A i j - ent B i j

@[expose] def smulM {N : Nat} (c : Rat) (A : Mat N) : Mat N := ofF fun i j => c * ent A i j

@[expose] def mulM {N : Nat} (A B : Mat N) : Mat N :=
  let ks := List.finRange N
  ofF fun i j => ks.foldl (fun acc k =>
    let a := ent A i k
    if a = 0 then acc else acc + a * ent B k j) 0

@[expose] def prodM {N : Nat} : List (Mat N) → Mat N
  | [] => oneM N
  | A :: As => mulM A (prodM As)

@[expose] def entN {a : Nat} (A : Mat a) (i j : Nat) : Rat :=
  if h : i < a then (if h' : j < a then ent A ⟨i, h⟩ ⟨j, h'⟩ else 0) else 0

@[expose] def kronM {a b : Nat} (A : Mat a) (B : Mat b) : Mat (a * b) :=
  ofF fun i j => entN A (i.val / b) (j.val / b) * entN B (i.val % b) (j.val % b)

@[expose] def mI : Mat 2 := oneM 2

@[expose] def mX : Mat 2 := ofF fun i j => if i.val + j.val = 1 then 1 else 0

@[expose] def mZ : Mat 2 := ofF fun i j => if i = j then (if i.val = 0 then 1 else -1) else 0

@[expose] def mJ : Mat 2 := ofF fun i j =>
  if i.val = 0 ∧ j.val = 1 then -1 else if i.val = 1 ∧ j.val = 0 then 1 else 0

@[expose] def str8Tab : List (List Nat) :=
  [[0, 1, 1, 1], [0, 2, 2, 2], [1, 0, 1, 2], [1, 1, 2, 0],
    [1, 2, 0, 1], [2, 0, 2, 1], [2, 1, 0, 2], [2, 2, 1, 0]]

@[expose] def str8 (k i : Nat) : Nat := (str8Tab.getD k []).getD i 0

@[expose] def letter (c : Nat) : Mat 2 := if c = 0 then mI else if c = 1 then mX else mZ

@[expose] def g8 (k : Nat) : Mat 16 :=
  kronM (kronM (kronM (letter (str8 k 0)) (letter (str8 k 1))) (letter (str8 k 2)))
    (letter (str8 k 3))

@[expose] def G8 (_ : Unit := ()) : Mat 16 := prodM (List.ofFn fun k : Fin 8 => g8 k)

@[expose] def gam8 (k : Nat) : Mat 16 := if k < 8 then g8 k else oneM 16

@[expose] def gam9 (k : Nat) : Mat 16 := if k < 8 then g8 k else G8 ()

@[expose] def gam10 (k : Nat) : Mat 32 :=
  if k < 8 then kronM (g8 k) mI
  else if k = 8 then kronM (G8 ()) mX else kronM (G8 ()) mZ

@[expose] def G10 (_ : Unit := ()) : Mat 32 := prodM (List.ofFn fun k : Fin 10 => gam10 k)

@[expose] def gam11 (k : Nat) : Mat 64 :=
  if k < 10 then kronM (gam10 k) mI else kronM (G10 ()) mJ

@[expose] def pairsS8 : List (List (Nat × Nat × Nat × Nat) × List (Nat × Nat × Nat × Nat)) :=
  [([(0, 4, 1, 2), (2, 4, 4, 6)], [(1, 6, 2, 3), (3, 6, 6, 7)]),
    ([(0, 5, 1, 3), (2, 3, 3, 6), (4, 6, 5, 7)], [(2, 3, 3, 7), (4, 6, 5, 7)]),
    ([(0, 4, 1, 5), (2, 3, 4, 6), (5, 7, 6, 7)], [(2, 7, 3, 6), (4, 7, 5, 6)]),
    ([(0, 1, 2, 3)], [(0, 2, 1, 3)])]

@[expose] def treeS8 : List (Nat × Nat) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 3), (3, 4), (4, 4), (4, 5), (5, 1), (5, 2), (5, 4), (6, 0), (7, 1), (7, 2), (7, 5), (8, 1), (8, 2), (8, 3), (8, 4), (9, 0), (9, 1), (9, 3), (9, 4), (10, 5), (11, 0), (12, 0), (12, 2), (12, 3), (12, 5), (13, 0), (13, 2), (13, 3), (13, 4), (14, 0), (14, 3), (14, 4), (15, 4), (16, 1), (16, 2), (16, 4), (17, 0), (17, 2), (17, 3), (17, 5), (18, 0), (18, 3), (18, 4), (19, 4), (20, 1), (20, 2), (20, 4), (21, 1), (21, 2), (22, 0), (23, 0), (23, 2), (23, 4), (24, 0), (24, 4), (25, 1), (25, 2), (26, 0), (26, 2), (26, 5), (27, 1), (27, 2), (27, 4), (28, 0), (28, 1), (28, 4), (29, 0), (30, 0), (30, 2), (30, 3), (30, 4), (31, 0), (31, 3), (31, 4), (33, 1), (33, 2), (34, 0), (34, 2), (34, 3), (34, 5), (35, 4), (37, 4), (38, 0), (39, 0), (39, 2), (39, 5), (40, 2), (43, 0), (44, 0), (44, 5), (46, 4), (47, 2), (49, 4), (50, 1), (50, 4), (51, 1), (52, 0), (52, 2), (53, 0), (58, 0), (66, 4), (67, 0), (67, 4), (68, 5), (71, 1), (81, 2), (82, 0), (82, 5), (84, 4)]

@[expose] def pairsA8 : List (List (Nat × Nat × Nat × Nat) × List (Nat × Nat × Nat × Nat)) :=
  [([(0, 1, 1, 6), (2, 5, 3, 5)], [(0, 1, 1, 7), (3, 5, 4, 5)]),
    ([(0, 6, 1, 4), (2, 3, 3, 4), (4, 6, 6, 7)], [(1, 5, 2, 5), (3, 6, 4, 7), (5, 6, 6, 7)]),
    ([(0, 1, 2, 3)], [(0, 2, 1, 3)])]

@[expose] def treeA8 : List (Nat × Nat) :=
  [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2), (4, 2)]

@[expose] def pairsS10 : List (List (Nat × Nat × Nat × Nat) × List (Nat × Nat × Nat × Nat)) :=
  [([(0, 9, 1, 8), (2, 6, 3, 8), (4, 8, 5, 7), (6, 9, 7, 8)], [(0, 1, 1, 4), (2, 7, 4, 8), (6, 7, 7, 8)]),
    ([(0, 2, 1, 2), (2, 6, 3, 8), (4, 7, 5, 9), (6, 7, 7, 8)], [(0, 5, 1, 5), (2, 8, 3, 7), (4, 8, 5, 7)]),
    ([(0, 5, 1, 9), (2, 9, 4, 9), (5, 7, 8, 9)], [(0, 4, 1, 3), (3, 6, 4, 7), (5, 6, 6, 9), (7, 8, 8, 9)]),
    ([(0, 6, 1, 9), (2, 4, 3, 8), (4, 8, 5, 7), (7, 9, 8, 9)], [(0, 2, 1, 4), (2, 8, 4, 6), (5, 8, 6, 7), (7, 8, 8, 9)]),
    ([(0, 1, 2, 3)], [(0, 2, 1, 3)])]

@[expose] def treeS10 : List (Nat × Nat) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 7), (2, 8), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 8), (4, 0), (4, 1), (4, 4), (4, 6), (5, 5), (5, 6), (5, 7), (5, 8), (6, 1), (6, 2), (6, 3), (6, 5), (6, 6), (6, 8), (7, 0), (7, 2), (7, 3), (7, 5), (7, 6), (7, 7), (8, 1), (8, 6), (8, 7), (8, 8), (9, 0), (9, 5), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 6), (10, 7), (10, 8), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 7), (11, 8), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 8), (13, 0), (13, 1), (13, 4), (13, 6), (14, 7), (14, 8), (15, 2), (15, 3), (15, 5), (15, 6), (15, 7), (16, 1), (16, 6), (16, 7), (16, 8), (17, 0), (17, 5), (18, 0), (18, 1), (18, 2), (18, 3), (18, 4), (18, 6), (19, 0), (19, 2), (19, 3), (19, 5), (20, 0), (20, 1), (20, 2), (20, 3), (20, 4), (20, 5), (20, 8), (21, 0), (21, 4), (21, 6), (22, 7), (22, 8), (23, 2), (23, 3), (23, 5), (23, 8), (24, 1), (24, 7), (24, 8), (25, 0), (26, 0), (26, 3), (26, 4), (26, 7), (26, 8), (27, 1), (27, 3), (27, 4), (27, 7), (27, 8), (28, 0), (28, 1), (28, 5), (30, 5), (30, 8), (31, 1), (31, 2), (31, 5), (31, 8), (32, 0), (32, 5), (33, 0), (33, 1), (33, 4), (34, 0), (34, 1), (34, 2), (34, 4), (35, 6), (36, 0), (36, 6), (36, 7), (37, 2), (37, 3), (37, 5), (37, 6), (37, 8), (38, 2), (38, 3), (38, 5), (38, 7), (39, 1), (39, 6), (40, 0), (40, 5), (42, 0), (42, 2), (42, 3), (44, 5), (44, 6), (45, 0), (45, 2), (47, 2), (47, 3), (48, 2), (49, 1), (51, 0), (53, 2), (54, 2), (54, 3), (55, 1), (57, 3), (58, 3), (59, 0), (59, 1), (59, 6), (60, 0), (60, 1), (60, 3), (60, 5), (60, 8), (61, 2), (62, 6), (64, 3), (64, 5), (64, 6), (64, 7), (65, 1), (65, 7), (67, 0), (67, 1), (67, 6), (68, 0), (68, 2), (68, 5), (69, 0), (69, 1), (69, 2), (69, 8), (72, 3), (72, 5), (73, 7), (75, 1), (75, 3), (75, 8), (76, 0), (76, 5), (79, 8), (80, 0), (80, 5), (81, 1), (81, 4), (82, 2), (83, 6), (84, 7), (85, 1), (87, 2), (90, 0), (92, 2), (93, 2), (93, 3), (96, 3), (97, 3), (101, 1), (103, 2), (104, 0), (105, 2), (105, 5), (109, 4), (112, 8), (115, 0), (117, 7), (119, 0), (129, 4), (134, 4), (142, 0), (149, 4), (150, 4)]

@[expose] def kleinS10 : List (Nat × Nat × Nat × Nat) :=
  [(5, 12, 78, 0), (5, 21, 116, 0), (5, 191, 230, 0), (5, 195, 203, 0), (5, 201, 217, 0), (5, 214, 242, 0), (5, 221, 243, 0), (12, 21, 221, 0), (12, 116, 243, 0), (12, 191, 217, 0), (12, 195, 242, 0), (12, 201, 230, 0), (12, 203, 214, 0), (21, 78, 243, 0), (21, 191, 242, 0), (21, 195, 217, 0), (21, 201, 203, 0), (21, 214, 230, 0), (78, 116, 221, 0), (78, 191, 201, 0), (78, 195, 214, 0), (78, 203, 242, 0), (78, 217, 230, 0), (116, 191, 214, 0), (116, 195, 201, 0), (116, 203, 217, 0), (116, 230, 242, 0), (191, 195, 221, 0), (191, 203, 243, 0), (195, 230, 243, 0), (201, 214, 221, 0), (201, 242, 243, 0), (203, 221, 230, 0), (214, 217, 243, 0), (217, 221, 242, 0), (5, 26, 130, 2), (5, 34, 155, 2), (5, 70, 133, 2), (5, 74, 105, 2), (5, 84, 231, 2), (5, 109, 246, 2), (5, 115, 181, 2), (5, 124, 157, 2), (5, 127, 250, 2), (5, 150, 255, 2), (5, 196, 220, 2), (5, 210, 235, 2), (5, 222, 239, 2), (5, 228, 248, 2), (26, 34, 230, 2), (26, 155, 191, 2), (26, 196, 210, 2), (26, 220, 235, 2), (26, 222, 248, 2), (26, 228, 239, 2), (34, 130, 191, 2), (34, 196, 239, 2), (34, 210, 228, 2), (34, 220, 222, 2), (34, 235, 248, 2), (70, 150, 230, 2), (70, 191, 255, 2), (74, 84, 191, 2), (74, 230, 231, 2), (84, 105, 230, 2), (105, 191, 231, 2), (109, 115, 230, 2), (109, 181, 191, 2), (115, 191, 246, 2), (124, 127, 230, 2), (124, 191, 250, 2), (127, 157, 191, 2), (130, 155, 230, 2), (130, 196, 235, 2), (130, 210, 220, 2), (130, 222, 228, 2), (130, 239, 248, 2), (133, 150, 191, 2), (133, 230, 255, 2), (155, 196, 222, 2), (155, 210, 248, 2), (155, 220, 239, 2), (155, 228, 235, 2), (157, 230, 250, 2), (181, 230, 246, 2), (191, 196, 248, 2), (191, 210, 222, 2), (191, 220, 228, 2), (191, 235, 239, 2), (196, 228, 230, 2), (210, 230, 239, 2), (220, 230, 248, 2), (222, 230, 235, 2), (5, 32, 142, 3), (5, 207, 227, 3), (32, 195, 227, 3), (32, 203, 207, 3), (142, 195, 207, 3), (142, 203, 227, 3), (5, 192, 236, 6), (5, 194, 234, 6), (192, 194, 243, 6), (192, 221, 234, 6), (194, 221, 236, 6), (234, 236, 243, 6), (5, 149, 254, 37), (70, 149, 192, 37), (70, 236, 254, 37), (133, 149, 236, 37), (133, 192, 254, 37), (74, 149, 207, 38), (74, 227, 254, 38), (105, 149, 227, 38), (105, 207, 254, 38), (5, 62, 179, 39), (62, 84, 192, 39), (62, 231, 236, 39), (84, 179, 236, 39), (179, 192, 231, 39), (5, 81, 229, 40), (32, 81, 246, 40), (32, 109, 229, 40), (81, 109, 142, 40), (142, 229, 246, 40), (5, 92, 233, 41), (92, 115, 194, 41), (92, 181, 234, 41), (115, 233, 234, 41), (181, 194, 233, 41), (81, 124, 234, 42), (81, 157, 194, 42), (124, 194, 229, 42), (157, 229, 234, 42), (32, 92, 250, 43), (32, 127, 233, 43), (92, 127, 142, 43), (142, 233, 250, 43), (62, 150, 207, 44), (62, 227, 255, 44), (150, 179, 227, 44), (179, 207, 255, 44), (32, 192, 210, 46), (32, 235, 236, 46), (142, 192, 235, 46), (142, 210, 236, 46), (194, 207, 239, 47), (194, 222, 227, 47), (207, 222, 234, 47), (227, 234, 239, 47)]

@[expose] def invS10 : List Nat :=
  [5, 12, 21, 26, 32, 34, 62, 70, 74, 78, 81, 84, 92, 105, 109, 115, 116, 124, 127, 130, 133, 142, 149, 150, 155, 157, 179, 181, 191, 192, 194, 195, 196, 201, 203, 207, 210, 214, 217, 220, 221, 222, 227, 228, 229, 230, 231, 233, 234, 235, 236, 239, 242, 243, 246, 248, 250, 254, 255]

abbrev Q4 : Type := Nat × Nat × Nat × Nat

abbrev Wd : Type := List Q4

@[expose] def Mdd {N : Nat} (Γ : Nat → Mat N) (q : Q4) : Mat N :=
  if q.1 = q.2.1 ∨ q.2.2.1 = q.2.2.2 then oneM N
  else smulM (1 / 2 : Rat) (mulM (subM (Γ q.1) (Γ q.2.1)) (subM (Γ q.2.2.1) (Γ q.2.2.2)))

@[expose] def Mw {N : Nat} (Γ : Nat → Mat N) (w : Wd) : Mat N := prodM (w.map (Mdd Γ))

@[expose] def invW (w : Wd) : Wd := (w.reverse).map fun q => (q.2.2.1, q.2.2.2, q.1, q.2.1)

@[expose] def Mcomm {N : Nat} (Γ : Nat → Mat N) (p : Wd × Wd) : Mat N :=
  mulM (mulM (mulM (Mw Γ p.1) (Mw Γ p.2)) (Mw Γ (invW p.1))) (Mw Γ (invW p.2))

@[expose] def gensM {N : Nat} (Γ : Nat → Mat N) (ps : List (Wd × Wd)) : List (Mat N) :=
  ps.map (Mcomm Γ) ++ ps.map fun p => Mcomm Γ (p.2, p.1)

@[expose] def treeAux {N : Nat} (gs : List (Mat N)) : List (Mat N) → List (Nat × Nat) → List (Mat N)
  | acc, [] => acc
  | acc, (p, g) :: tr => treeAux gs (acc ++ [mulM (gs.getD g (oneM N)) (acc.getD p (oneM N))]) tr

@[expose] def treeTab {N : Nat} (gs : List (Mat N)) (tr : List (Nat × Nat)) : List (Mat N) :=
  treeAux gs [oneM N] tr

@[expose] def gamRelB {N : Nat} (Γ : Nat → Mat N) (n : Nat) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j =>
    decide (addM (mulM (Γ i) (Γ j)) (mulM (Γ j) (Γ i)) =
      if i = j then smulM 2 (oneM N) else zeroM N)

@[expose] def closedB {N : Nat} (T gs : List (Mat N)) : Bool :=
  decide T.Nodup && T.all fun x => gs.all fun g => decide (mulM g x ∈ T)

@[expose] def wordsOK (n : Nat) (ps : List (List (Nat × Nat × Nat × Nat) × List (Nat × Nat × Nat × Nat))) : Bool :=
  ps.all fun p => (p.1 ++ p.2).all fun q =>
    decide (q.1 < n ∧ q.2.1 < n ∧ q.2.2.1 < n ∧ q.2.2.2 < n ∧ q.1 ≠ q.2.1 ∧ q.2.2.1 ≠ q.2.2.2)

@[expose] def normalCheck {N : Nat} (Γ : Nat → Mat N) (n : Nat) : Bool :=
  let one := oneM N
  let gS := gensM Γ pairsS8
  let T := treeTab gS treeS8
  let gA := gensM Γ pairsA8
  let TA := treeTab gA treeA8
  gamRelB Γ n && wordsOK n pairsS8 && wordsOK n pairsA8 && closedB T gS && decide (T.length = 128) &&
    closedB TA gA && decide (TA.length = 8) &&
    TA.all (fun x => decide (mulM x x = one)) &&
    gS.all fun g => gA.all fun a => TA.any fun b => decide (mulM g a = mulM b g)

@[expose] def kleinCheck {N : Nat} (Γ : Nat → Mat N) (n : Nat) : Bool :=
  let one := oneM N
  let gS := gensM Γ pairsS10
  let T := treeTab gS treeS10
  let KL := kleinS10
  let Iv := invS10
  gamRelB Γ n && wordsOK n pairsS10 && closedB T gS && decide (T.length = 256) &&
    KL.all (fun k => decide (mulM (T.getD k.1 one) (T.getD k.1 one) = one) &&
      decide (mulM (T.getD k.2.1 one) (T.getD k.2.1 one) = one) &&
      decide (mulM (T.getD k.1 one) (T.getD k.2.1 one) = mulM (T.getD k.2.1 one) (T.getD k.1 one)) &&
      decide (T.getD k.1 one ≠ one) && decide (T.getD k.2.1 one ≠ one) &&
      decide (T.getD k.1 one ≠ T.getD k.2.1 one) &&
      decide (T.getD k.2.2.1 one = mulM (T.getD k.1 one) (T.getD k.2.1 one))) &&
    ((List.range KL.length).all fun idx =>
      decide (idx = 0) || (decide ((KL.getD idx (0, 0, 0, 0)).2.2.2 < idx) &&
        (let k := KL.getD idx (0, 0, 0, 0)
         let kp := KL.getD k.2.2.2 (0, 0, 0, 0)
         decide (mulM (T.getD k.1 one) (T.getD kp.1 one) = mulM (T.getD kp.1 one) (T.getD k.1 one)) &&
         decide (mulM (T.getD k.1 one) (T.getD kp.2.1 one) = mulM (T.getD kp.2.1 one) (T.getD k.1 one)) &&
         decide (mulM (T.getD k.2.1 one) (T.getD kp.1 one) = mulM (T.getD kp.1 one) (T.getD k.2.1 one)) &&
         decide (mulM (T.getD k.2.1 one) (T.getD kp.2.1 one) = mulM (T.getD kp.2.1 one) (T.getD k.2.1 one))))) &&
    (List.range T.length).all (fun i =>
      decide ((decide (mulM (T.getD i one) (T.getD i one) = one ∧ T.getD i one ≠ one)) =
        decide (i ∈ Iv))) &&
    Iv.all fun i => Iv.all fun j =>
      decide (i = j) || !(decide (mulM (T.getD i one) (T.getD j one) =
        mulM (T.getD j one) (T.getD i one))) ||
        KL.any fun k => decide (i ∈ [0, k.1, k.2.1, k.2.2.1]) && decide (j ∈ [0, k.1, k.2.1, k.2.2.1])

end CFSG.ComponentClassification.Sol76.Sig.GSYard02.SpinNative

end
