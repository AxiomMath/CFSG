module

public import Std.Data.HashSet

public section

namespace CFSG.KGroups.Sp6

@[expose] def bf (x y : Nat) : Bool :=
  (x.testBit 0 && y.testBit 3) ^^ (x.testBit 3 && y.testBit 0) ^^
  (x.testBit 1 && y.testBit 4) ^^ (x.testBit 4 && y.testBit 1) ^^
  (x.testBit 2 && y.testBit 5) ^^ (x.testBit 5 && y.testBit 2)

@[expose] def mulVecC (A : List Nat) (v : Nat) : Nat :=
  (if v.testBit 0 then A.getD 0 0 else 0) ^^^ (if v.testBit 1 then A.getD 1 0 else 0) ^^^
  (if v.testBit 2 then A.getD 2 0 else 0) ^^^ (if v.testBit 3 then A.getD 3 0 else 0) ^^^
  (if v.testBit 4 then A.getD 4 0 else 0) ^^^ (if v.testBit 5 then A.getD 5 0 else 0)

@[expose] def mulC (A B : List Nat) : List Nat := B.map (mulVecC A)

@[expose] def oneC : List Nat := [1, 2, 4, 8, 16, 32]

@[expose] def powC (s : List Nat) : Nat → List Nat
  | 0 => oneC
  | k + 1 => mulC s (powC s k)

@[expose] def cand0 (c : Nat) : Bool := c != 0

@[expose] def cand1 (a c : Nat) : Bool := c != 0 && !bf a c

@[expose] def cand2 (a b c : Nat) : Bool := c != 0 && !bf a c && !bf b c

@[expose] def cand3 (a b d c : Nat) : Bool := c != 0 && bf a c && !bf b c && !bf d c

@[expose] def cand4 (a b d e c : Nat) : Bool :=
  c != 0 && !bf a c && bf b c && !bf d c && !bf e c

@[expose] def cand5 (a b d e f c : Nat) : Bool :=
  c != 0 && !bf a c && !bf b c && bf d c && !bf e c && !bf f c

@[expose] def spCount (r : Nat) (P : List Nat → Bool) : Nat :=
  (((List.range r).filter cand0).map fun c0 =>
    (((List.range r).filter (cand1 c0)).map fun c1 =>
      (((List.range r).filter (cand2 c0 c1)).map fun c2 =>
        (((List.range r).filter (cand3 c0 c1 c2)).map fun c3 =>
          (((List.range r).filter (cand4 c0 c1 c2 c3)).map fun c4 =>
            (((List.range r).filter (cand5 c0 c1 c2 c3 c4)).map fun c5 =>
              if P [c0, c1, c2, c3, c4, c5] then 1 else 0).sum).sum).sum).sum).sum).sum

@[expose] def countCheck (r n : Nat) : Bool := spCount r (fun _ => true) == n

@[expose] def five (z : List Nat) : Bool :=
  let z2 := mulC z z
  let z3 := mulC z2 z
  let y := mulC z3 z3
  y != oneC && mulC y (mulC (mulC y y) (mulC y y)) == oneC

@[expose] def normCheck (r : Nat) (s : List Nat) (N : List (List Nat)) : Bool :=
  let P := (List.range 6).map fun k => powC s (k + 1)
  spCount r (fun x => P.any (fun p => mulC x s == mulC p x) && !N.contains x) == 0

@[expose] def witCheck (r : Nat) (G N : List (List Nat)) (bound : Nat) : Bool :=
  let gs : Std.HashSet (List Nat) := Std.HashSet.ofList G
  decide (spCount r (fun x => !gs.contains x && !N.any fun n => five (mulC x n)) ≤ bound)

@[expose] def s0 : List Nat := [16, 33, 28, 19, 4, 1]

@[expose] def n0List : List (List Nat) :=
  [[1, 2, 4, 8, 16, 32], [1, 20, 34, 9, 32, 16], [4, 17, 11, 53, 28, 16], [4, 23, 1, 49, 16, 28],
   [6, 5, 57, 21, 54, 56], [6, 15, 61, 19, 56, 54], [10, 59, 27, 3, 36, 38],
   [10, 63, 29, 9, 38, 36], [11, 2, 4, 8, 28, 34], [11, 24, 32, 3, 34, 28],
   [16, 24, 32, 3, 1, 4], [16, 33, 28, 19, 4, 1], [22, 5, 57, 21, 26, 61],
   [22, 35, 56, 3, 61, 26], [26, 15, 61, 19, 22, 57], [26, 43, 54, 9, 57, 22],
   [27, 14, 10, 8, 36, 60], [27, 46, 50, 19, 60, 36], [28, 20, 34, 9, 11, 4],
   [28, 41, 16, 21, 4, 11], [29, 14, 10, 8, 38, 50], [29, 44, 60, 21, 50, 38],
   [32, 17, 11, 53, 34, 1], [32, 41, 16, 21, 1, 34], [34, 23, 1, 49, 32, 11],
   [34, 33, 28, 19, 11, 32], [36, 39, 38, 49, 10, 27], [36, 44, 60, 21, 27, 10],
   [38, 46, 50, 19, 29, 10], [38, 47, 36, 53, 10, 29], [50, 39, 38, 49, 29, 60],
   [50, 59, 27, 3, 60, 29], [54, 35, 56, 3, 6, 57], [54, 62, 26, 53, 57, 6],
   [56, 43, 54, 9, 6, 61], [56, 48, 22, 49, 61, 6], [57, 12, 6, 8, 54, 26],
   [57, 48, 22, 49, 26, 54], [60, 47, 36, 53, 27, 50], [60, 63, 29, 9, 50, 27],
   [61, 12, 6, 8, 56, 22], [61, 62, 26, 53, 22, 56]]

end CFSG.KGroups.Sp6
