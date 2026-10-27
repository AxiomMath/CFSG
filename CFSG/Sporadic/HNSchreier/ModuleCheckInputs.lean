module

public import CFSG.Sporadic.HNSchreier.SeedsCheck
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.Sporadic.He.Native

@[expose] def rightNull : String :=
  "033003323001044421020343023233443203132213144130411333410324400400313421442420413322133123" ++
    "1440404124114241433241324142023014314201000"

@[expose] def leftNull : String :=
  "021404341202421414122012111044433304121134140043414224102324013043300330203441041322310141" ++
    "3110121031403332431140202321122423031240441"

@[expose] def colParents : List (Nat × Nat) := [
    (0, 0), (0, 1), (0, 2), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2), (4, 2), (5, 1), (6, 2), (8, 1),
    (8, 2), (9, 2), (10, 2), (11, 2), (12, 1), (13, 1), (13, 2), (14, 1), (15, 1), (15, 2), (16, 2),
    (17, 2), (18, 1), (19, 2), (20, 2), (21, 1), (22, 1), (22, 2), (23, 1), (23, 2), (24, 2),
    (25, 1), (25, 2), (26, 1), (26, 2), (27, 2), (28, 2), (29, 1), (30, 2), (31, 1), (32, 1),
    (32, 2), (33, 2), (34, 1), (35, 2), (36, 1), (37, 1), (37, 2), (38, 1), (38, 2), (39, 2),
    (40, 1), (40, 2), (41, 2), (42, 2), (43, 1), (44, 1), (44, 2), (45, 2), (46, 1), (46, 2),
    (47, 2), (48, 2), (49, 1), (50, 2), (51, 1), (52, 1), (52, 2), (53, 2), (54, 1), (55, 1),
    (55, 2), (56, 1), (56, 2), (57, 2), (58, 2), (59, 1), (60, 1), (60, 2), (61, 2), (62, 1),
    (63, 1), (63, 2), (64, 1), (64, 2), (65, 2), (66, 1), (66, 2), (67, 2), (68, 2), (69, 1),
    (70, 1), (70, 2), (71, 2), (72, 2), (73, 1), (74, 2), (76, 1), (76, 2), (77, 1), (77, 2),
    (78, 2), (79, 2), (80, 1), (81, 1), (81, 2), (82, 2), (83, 2), (84, 1), (85, 2), (87, 1),
    (87, 2), (88, 2), (89, 1), (90, 2), (91, 1), (91, 2), (92, 2), (93, 2), (94, 1), (95, 1),
    (95, 2), (96, 2), (97, 2), (98, 1), (98, 2), (99, 2), (100, 1), (101, 2), (103, 2), (105, 2)]

@[expose] def rowParents : List (Nat × Nat) := [
    (0, 0), (0, 1), (0, 2), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2), (4, 2), (6, 2), (7, 1), (8, 2),
    (9, 1), (9, 2), (10, 2), (11, 1), (12, 2), (13, 1), (14, 1), (14, 2), (15, 2), (16, 1), (16, 2),
    (17, 2), (18, 2), (19, 1), (20, 1), (20, 2), (21, 2), (22, 1), (23, 1), (23, 2), (24, 1),
    (24, 2), (25, 2), (26, 2), (27, 1), (28, 1), (28, 2), (29, 2), (30, 2), (31, 1), (32, 2),
    (33, 1), (34, 1), (34, 2), (35, 1), (35, 2), (36, 2), (37, 2), (38, 1), (39, 1), (39, 2),
    (40, 1), (40, 2), (41, 2), (42, 1), (42, 2), (43, 2), (44, 2), (45, 1), (46, 2), (47, 1),
    (48, 1), (48, 2), (49, 1), (49, 2), (50, 2), (51, 2), (52, 1), (53, 2), (54, 1), (55, 1),
    (55, 2), (56, 2), (57, 1), (58, 1), (58, 2), (59, 1), (59, 2), (60, 2), (61, 1), (61, 2),
    (62, 2), (63, 2), (64, 1), (65, 2), (66, 1), (67, 1), (67, 2), (68, 1), (68, 2), (69, 2),
    (70, 1), (70, 2), (71, 2), (72, 2), (73, 1), (74, 1), (74, 2), (75, 2), (76, 2), (77, 1),
    (78, 2), (80, 1), (80, 2), (81, 2), (82, 1), (83, 2), (84, 1), (84, 2), (85, 2), (86, 1),
    (86, 2), (87, 2), (88, 2), (89, 1), (90, 2), (92, 1), (92, 2), (93, 2), (94, 1), (95, 2),
    (96, 1), (96, 2), (97, 2), (98, 2), (99, 1), (100, 1), (100, 2), (102, 2), (103, 2), (106, 2)]

@[expose] def digitVec (s : String) : Array Nat :=
  (s.toList.map fun c => c.toNat - '0'.toNat).toArray

@[expose] def cRows (A B : Array (Array Nat)) : Array (Array Nat) :=
  let W1 := wordM (seedSel A B) [2, 1, 2, 1]
  let W2 := wordM (seedSel A B) [2, 1]
  let W4 := wordM (seedSel A B) [1, 2, 2, 1]
  let W5 := wordM (seedSel A B) [2, 2]
  Array.ofFn (n := 133) fun i => Array.ofFn (n := 133) fun j =>
    (W1[i]![j]! + 3 * W2[i]![j]! + 2 * B[i]![j]! + 4 * W4[i]![j]! + W5[i]![j]!) % 5

@[inline, expose] def skipOne (k : Nat) : Nat := if k < 1 then k else k + 1

@[expose] def minorRows (X : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (n := 132) fun i => Array.ofFn (n := 132) fun j => X[skipOne i.val]![skipOne j.val]!

@[expose] def recVecs (w : Array Nat) (step : Nat → Array Nat → Array Nat)
    (recs : List (Nat × Nat)) : Array (Array Nat) :=
  (recs.drop 1).foldl (fun acc r => acc.push (step r.2 acc[r.1]!)) #[w]

@[expose] def recOK (w : Array Nat) (step : Nat → Array Nat → Array Nat) (recs : List (Nat × Nat))
    (vs : Array (Array Nat)) : Bool :=
  recs.length == 133 && vs.size == 133 && vs[0]! == w &&
    (List.range 133).all fun i => i == 0 || (decide (recs[i]!.1 < i) &&
      (recs[i]!.2 == 1 || recs[i]!.2 == 2) && vs[i]! == step recs[i]!.2 vs[recs[i]!.1]!)

@[expose] def colStep (A B : Array (Array Nat)) (l : Nat) (x : Array Nat) : Array Nat :=
  mulVec 5 133 (seedSel A B l) x

@[expose] def rowStep (A B : Array (Array Nat)) (l : Nat) (x : Array Nat) : Array Nat :=
  mulVec 5 133 (colsMat 133 (seedSel A B l)) x

@[expose] def colVecs (A B : Array (Array Nat)) : Array (Array Nat) :=
  recVecs (digitVec rightNull) (colStep A B) colParents

@[expose] def rowVecs (A B : Array (Array Nat)) : Array (Array Nat) :=
  recVecs (digitVec leftNull) (rowStep A B) rowParents

@[expose] def zeroV : Array Nat := Array.replicate 133 0

@[noinline, expose] def moduleChecks (A B : Array (Array Nat)) : Bool :=
  let C := cRows A B
  let v := digitVec rightNull
  let u := digitVec leftNull
  let Mn := minorRows C
  let Mc := colsMat 133 (colVecs A B)
  let Mr := rowVecs A B
  v.size == 133 && u.size == 133 && v.all (· < 5) && u.all (· < 5) && v.any (· != 0) &&
    u.any (· != 0) && mulVec 5 133 C v == zeroV && mulVec 5 133 (colsMat 133 C) u == zeroV &&
    mulM 5 132 Mn (invM 5 132 Mn) == idM 132 &&
    recOK (digitVec rightNull) (colStep A B) colParents (colVecs A B) &&
    recOK (digitVec leftNull) (rowStep A B) rowParents Mr &&
    mulM 5 133 Mc (invM 5 133 Mc) == idM 133 && mulM 5 133 Mr (invM 5 133 Mr) == idM 133

end CFSG.Sporadic.HNSchreier.Native
