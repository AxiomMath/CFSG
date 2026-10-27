module

public import Certificates.Data.SmithL6Model

public section

namespace CFSG.SmithL6

open CFSG.SmithE (tri applyCols)

@[expose] def tvIdxTab : Array Nat :=
  (List.range 1953).foldl (fun A k => A.set! (64 * (tvPair k).1 + (tvPair k).2) k)
    (Array.replicate 4096 1953)

@[expose] def tvImg (j a : Nat) : Nat :=
  let p := tvPair j
  let q := tvPair a
  tvIdxTab[64 * (if form p.2 q.1 then q.1 ^^^ p.1 else q.1) +
    (if form q.2 p.1 then q.2 ^^^ p.2 else q.2)]!

@[expose] def tvTab : Array (Array Nat) :=
  Array.ofFn (n := 1953) fun j => Array.ofFn (n := 1953) fun a => tvImg j.val a.val

@[expose] def tvArr : Array (Array Nat) := Array.ofFn (n := 1953) fun k => tvCols k.val

@[expose] def chkTvList : Bool :=
  tvList.size == 1953 &&
  (List.range 1953).all (fun k => let p := tvPair k
    decide (p.1 < 64) && decide (p.2 < 64) && p.1 != 0 && p.2 != 0 && !form p.2 p.1 &&
      tvIdxTab[64 * p.1 + p.2]! == k) &&
  (List.range 4096).all (fun n => let k := tvIdxTab[n]!
    decide (k ≤ 1953) && (k == 1953 || tvPair k == (n / 64, n % 64))) &&
  (List.range 4096).all fun n =>
    n / 64 == 0 || n % 64 == 0 || form (n % 64) (n / 64) || decide (tvIdxTab[n]! < 1953)

@[expose] def chkTvInv : Bool :=
  (List.range 1953).all fun k => let T := tvArr[k]!
    T.size == 20 &&
      (List.range 20).all fun m => decide (T[m]! < 2 ^ 20) && applyCols T T[m]! == 2 ^ m

@[expose] def chkTvImg : Bool :=
  (List.range 1953).all fun j => let row := tvTab[j]!
    (List.range 1953).all fun a => let b := row[a]!
      decide (b < 1953) && row[b]! == a

@[expose] def wtArr : Array Nat := Array.ofFn (n := 1395) fun i => wt i.val

@[expose] def maskArr : Array Nat := Array.ofFn (n := 1395) fun i => wMask i.val

@[expose] def annMaskOf (a b c : Nat) : Nat :=
  (List.range 64).foldl
    (fun acc φ => if !form φ a && !form φ b && !form φ c then acc ||| 2 ^ φ else acc) 0

@[expose] def annArr : Array Nat :=
  Array.ofFn (n := 1395) fun i => let W := wB i.val; annMaskOf W.1 W.2.1 W.2.2

@[expose] def wtIdx : Array Nat :=
  (List.range 1395).foldl (fun A j => A.set! wtArr[j]! j) (Array.replicate (2 ^ 20) 1395)

@[expose] def inPlane (i a : Nat) : Bool :=
  let p := tvPair a
  maskArr[i]!.testBit p.1 && annArr[i]!.testBit p.2

@[expose] def planePts (i : Nat) : Array Nat := ((List.range 1953).filter (inPlane i)).toArray

@[expose] def planePtsArr : Array (Array Nat) := Array.ofFn (n := 1395) fun i => planePts i.val

@[expose] def flagArr : Array (Array Bool) :=
  Array.ofFn (n := 1395) fun j => Array.ofFn (n := 1953) fun a => inPlane j.val a.val

@[expose] def planeImg (k i : Nat) : Nat := wtIdx[applyCols tvArr[k]! wtArr[i]!]!

@[expose] def meetCard (i j : Nat) : Nat := planePtsArr[i]!.countP fun a => flagArr[j]![a]!

@[expose] def distB (i j : Nat) : Nat :=
  let c := meetCard i j
  if c == 49 then 0 else if c == 9 then 1 else if c == 1 then 2 else 3

@[expose] def relB (R i j : Nat) : Bool := R.testBit (distB i j)

@[expose] def adjM (i j : Nat) : Bool := atLeast4 (maskArr[i]! &&& maskArr[j]!)

@[expose] def chkPairs : Bool :=
  (List.range 1395).all fun i => (List.range 1395).all fun j =>
    let c := meetCard i j
    (if i == j then c == 49 else c == 0 || c == 1 || c == 9) &&
      fB wtArr[i]! wtArr[j]! == (c == 0) && adjM i j == decide (9 ≤ c)

@[expose] def chkTW : Bool :=
  (List.range 1953).all fun k => let T := tvArr[k]!; let row := tvTab[k]!
    (List.range 1395).all fun i => let j := planeImg k i
      decide (j < 1395) && wtArr[j]! == applyCols T wtArr[i]! &&
        planePtsArr[i]!.all fun a => flagArr[j]![row[a]!]!

@[expose] def chkFormInv : Bool :=
  (List.range 1953).all fun k => let T := tvArr[k]!
    (List.range 20).all fun a => (List.range 20).all fun b => fB T[a]! T[b]! == fB (2 ^ a) (2 ^ b)

end CFSG.SmithL6
