module

public section

namespace Timmesfeld.Fi24Fix

@[expose] def mmulL (p n : Nat) (A B : List Nat) : List Nat :=
  let Aa := A.toArray
  let Ba := B.toArray
  (List.range (n * n)).map fun idx =>
    ((List.range n).foldl
      (fun acc j => acc + Aa.getD (n * (idx / n) + j) 0 * Ba.getD (n * j + idx % n) 0) 0) % p

@[expose] def midL (p n : Nat) : List Nat :=
  (List.range (n * n)).map fun idx => if idx / n = idx % n then 1 % p else 0

@[expose] def mpowL (p n : Nat) (A : List Nat) : Nat → List Nat
  | 0 => midL p n
  | e + 1 => mmulL p n A (mpowL p n A e)

@[expose] def wordsL (p n : Nat) : List (List Nat) → List (List Nat)
  | [] => [midL p n]
  | A :: As => (wordsL p n As).flatMap fun M =>
      (List.range p).map fun a => mmulL p n (mpowL p n A a) M

@[expose] def allVecs (p : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (List.range p).flatMap fun a => (allVecs p n).map (a :: ·)

@[expose] def o3L (Lm : List (List Nat)) : List (List Nat) :=
  Lm.filter fun M => M != midL 3 7 && mmulL 3 7 (mmulL 3 7 M M) M == midL 3 7

@[expose] def matVecA (Ma : Array Nat) (c : List Nat) : List Nat :=
  (List.range 7).map fun k =>
    ((List.range 7).foldl (fun s i => s + Ma.getD (7 * k + i) 0 * c.getD i 0) 0) % 3

@[expose] def fixesA (Ma : Array Nat) (v : List Nat) : Bool := matVecA Ma v == v

@[expose] def nfixA (Ma : Array Nat) : Nat := ((allVecs 3 7).filter (fixesA Ma)).length

@[expose] def fi24Check (Lm : List (List Nat)) : Bool :=
  let O := (o3L Lm).map fun M => (M.toArray, nfixA M.toArray)
  let T5 := O.filter fun x => 243 ≤ x.2
  decide (O.length < 6560) && O.all (fun x => x.2 ≤ 243) &&
  decide (((allVecs 3 7).filter fun v => 2186 ≤ (O.filter fun x => fixesA x.1 v).length).length
    ≤ 26) &&
  decide (((allVecs 3 7).filter fun v => 728 ≤ (O.filter fun x => fixesA x.1 v).length).length
    ≤ 80) &&
  decide (((allVecs 3 7).filter fun v => 242 ≤ (T5.filter fun x => fixesA x.1 v).length).length
    ≤ 242)

@[expose] def fi24Tops : List (List Nat) := [
  [0, 2, 2, 1, 2, 1, 1,
   0, 0, 2, 2, 1, 2, 2,
   2, 0, 1, 1, 0, 0, 0,
   2, 2, 2, 2, 1, 0, 2,
   2, 2, 2, 1, 0, 1, 1,
   1, 1, 1, 2, 1, 0, 2,
   2, 0, 0, 0, 0, 2, 1],
  [1, 0, 2, 0, 2, 2, 0,
   0, 1, 0, 0, 0, 0, 1,
   0, 0, 1, 0, 0, 0, 2,
   0, 0, 2, 1, 2, 2, 2,
   0, 0, 2, 0, 0, 2, 2,
   0, 0, 1, 0, 1, 2, 0,
   0, 0, 0, 0, 0, 0, 1],
  [0, 0, 1, 0, 2, 1, 0,
   0, 1, 1, 2, 0, 2, 1,
   2, 0, 1, 0, 0, 2, 0,
   2, 0, 1, 1, 2, 1, 1,
   0, 0, 1, 0, 0, 2, 0,
   1, 0, 2, 0, 1, 0, 0,
   0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 1, 0, 0,
   1, 1, 0, 1, 0, 2, 1,
   0, 0, 1, 2, 2, 1, 2,
   1, 0, 0, 1, 2, 0, 0,
   2, 0, 0, 0, 2, 0, 0,
   1, 0, 0, 0, 2, 1, 0,
   0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 2, 0, 1, 0,
   1, 1, 0, 1, 0, 2, 0,
   1, 0, 1, 0, 0, 1, 1,
   0, 0, 0, 0, 0, 2, 1,
   2, 0, 0, 2, 1, 1, 0,
   1, 0, 0, 1, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 1, 2, 2, 1,
   0, 1, 0, 1, 2, 0, 1,
   0, 0, 1, 0, 0, 0, 0,
   0, 0, 0, 2, 2, 0, 1,
   2, 0, 0, 1, 0, 2, 1,
   1, 0, 0, 2, 1, 2, 2,
   0, 0, 0, 0, 0, 0, 1],
  [2, 0, 0, 0, 1, 2, 1,
   2, 1, 0, 0, 2, 1, 2,
   2, 0, 1, 0, 0, 2, 2,
   1, 0, 0, 1, 1, 2, 1,
   1, 0, 0, 0, 2, 2, 1,
   2, 0, 0, 0, 2, 2, 2,
   0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 2, 1, 2,
   2, 1, 0, 0, 2, 1, 2,
   2, 0, 1, 0, 0, 2, 0,
   2, 0, 0, 1, 2, 1, 2,
   2, 0, 0, 0, 0, 1, 2,
   1, 0, 0, 0, 1, 0, 1,
   0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 2, 1,
   0, 1, 0, 0, 0, 0, 1,
   0, 0, 1, 0, 0, 0, 0,
   2, 0, 0, 1, 0, 2, 1,
   2, 0, 0, 0, 1, 2, 1,
   1, 0, 0, 0, 0, 2, 2,
   0, 0, 0, 0, 0, 0, 1]]

@[expose] def fi24Matrices : List (List Nat) := wordsL 3 7 fi24Tops

end Timmesfeld.Fi24Fix
