module

public import Std.Data.HashMap

public section

namespace HNUnitaryBridge

@[expose] def fadd (x y : Nat) : Nat :=
  (x % 5 + y % 5) % 5 + 5 * ((x / 5 % 5 + y / 5 % 5) % 5)

@[expose] def fmul (x y : Nat) : Nat :=
  (x % 5 * (y % 5) + 2 * (x / 5 % 5) * (y / 5 % 5)) % 5 +
    5 * ((x % 5 * (y / 5 % 5) + x / 5 % 5 * (y % 5)) % 5)

@[expose] def finv (c : Nat) : Nat := ((List.range 25).find? fun y => fmul c y == 1).getD 0

@[expose] def smallPermLists : Array (List Nat) := #[
    [0, 47, 23, 26, 39, 36, 28, 42, 18, 6, 16, 35, 43, 1, 31, 14, 29, 49, 40, 19, 12, 21, 48, 44, 5, 17, 46, 22, 9, 10, 32, 15, 45, 33, 7, 37, 24, 11, 38, 41, 8, 4, 34, 20, 2, 30, 3, 13, 27, 25],
    [0, 23, 34, 45, 6, 26, 9, 44, 14, 4, 1, 5, 48, 7, 15, 8, 2, 49, 31, 19, 22, 17, 27, 10, 30, 25, 11, 20, 41, 42, 46, 40, 36, 33, 16, 3, 37, 32, 38, 28, 18, 39, 47, 12, 13, 35, 24, 29, 43, 21],
    [0, 27, 36, 47, 41, 2, 4, 20, 15, 28, 7, 12, 34, 46, 40, 18, 43, 49, 8, 19, 10, 21, 13, 24, 44, 25, 32, 30, 39, 35, 1, 14, 48, 17, 11, 42, 5, 16, 38, 9, 31, 6, 29, 37, 23, 3, 22, 45, 26, 33],
    [0, 40, 44, 29, 9, 24, 41, 15, 13, 39, 46, 31, 27, 16, 34, 37, 8, 49, 10, 19, 43, 21, 20, 5, 23, 25, 1, 48, 6, 47, 11, 30, 14, 33, 32, 45, 2, 7, 17, 4, 26, 28, 35, 22, 36, 42, 18, 3, 12, 38],
    [0, 4, 5, 35, 34, 23, 10, 41, 40, 26, 11, 6, 20, 32, 8, 31, 9, 49, 15, 17, 27, 21, 43, 2, 36, 25, 16, 12, 37, 3, 7, 18, 39, 33, 1, 29, 44, 46, 38, 13, 14, 30, 45, 48, 24, 47, 28, 42, 22, 19],
    [14, 13, 8, 9, 1, 40, 33, 7, 32, 3, 16, 29, 34, 22, 45, 17, 21, 41, 39, 43, 42, 38, 4, 18, 0, 47, 26, 2, 6, 37, 23, 36, 27, 46, 19, 11, 31, 35, 10, 30, 48, 44, 20, 12, 15, 24, 28, 25, 49, 5]]

@[expose] def smallPerms : Array (Array Nat) := smallPermLists.map List.toArray

@[expose] def composeArr (p q : Array Nat) : Array Nat := q.map fun y => p[y]!

@[expose] def idPerm : Array Nat := Array.range 50

@[expose] def evalWord (ws : List Nat) : Array Nat :=
  ws.foldr (fun w acc => composeArr smallPerms[w]! acc) idPerm

@[expose] def wordB : List Nat := [5, 4, 4, 5, 2, 2, 0, 2, 0, 0, 3, 2, 3, 3, 1, 2, 2, 1, 3, 5]

@[expose] def sigmaA : Array Nat := smallPerms[0]!

@[expose] def sigmaB : Array Nat := evalWord wordB

@[expose] def evalAB (L : List Bool) : Array Nat :=
  L.foldr (fun b acc => composeArr (if b then sigmaB else sigmaA) acc) idPerm

@[expose] def wordsAB : List (List Bool) :=
  [[false],
   [false, false, true, true, false, true, false, true, true, true, true, false, true, true, true,
    false],
   [true, false, true, false, false, true, true, false, true, false, true, false, false, true, true],
   [true, true, false, false, true, true, false, true, false, true, true, false, true, true, false,
    false, true, false],
   [true, true, false, true, true, false, false, true, false, false, true, true, false, false, true,
    true, false, true],
   [true, true, false, true, true, false, true, true, false, false, true, false, true, false, true,
    true, true, false, false, true, false, true]]

@[expose] def wordsOK : Bool := (List.range 6).all fun k => evalAB wordsAB[k]! == smallPerms[k]!

@[expose] def uCode : Array Nat := #[0, 0, 1, 1, 0, 0, 0, 1, 0]

@[expose] def vCode : Array Nat := #[6, 0, 10, 0, 1, 0, 10, 0, 21]

@[expose] def idMat : Array Nat := #[1, 0, 0, 0, 1, 0, 0, 0, 1]

@[expose] def idCode (k : Nat) : Nat := if k = 0 ∨ k = 4 ∨ k = 8 then 1 else 0

@[expose] def mprod (A B : Nat → Nat) (k : Nat) : Nat :=
  fadd (fadd (fmul (A (3 * (k / 3))) (B (k % 3))) (fmul (A (3 * (k / 3) + 1)) (B (3 + k % 3))))
    (fmul (A (3 * (k / 3) + 2)) (B (6 + k % 3)))

@[expose] def firstNZ (f : Nat → Nat) : Nat :=
  if f 0 ≠ 0 then f 0 else if f 1 ≠ 0 then f 1 else if f 2 ≠ 0 then f 2 else
  if f 3 ≠ 0 then f 3 else if f 4 ≠ 0 then f 4 else if f 5 ≠ 0 then f 5 else
  if f 6 ≠ 0 then f 6 else if f 7 ≠ 0 then f 7 else f 8

structure Table where
  n : Nat
  perm : Nat → Nat → Nat
  mat : Nat → Nat → Nat
  sa : Nat → Nat
  sb : Nat → Nat

@[expose] def Table.ofArrays (perms mats : Array (Array Nat)) (sa sb : Array Nat) : Table where
  n := perms.size
  perm := fun i x => (perms[i]!)[x]!
  mat := fun i k => (mats[i]!)[k]!
  sa := fun i => sa[i]!
  sb := fun i => sb[i]!

@[expose] def normMat (P : Array Nat) : Array Nat :=
  let ci := finv (firstNZ fun k => P[k]!)
  P.map fun y => fmul ci y

@[expose] def mmulArr (M X : Array Nat) : Array Nat :=
  (Array.range 9).map fun k => mprod (fun i => M[i]!) (fun i => X[i]!) k

@[expose] def genTable : Table := Id.run do
  let mut perms : Array (Array Nat) := #[idPerm]
  let mut mats : Array (Array Nat) := #[idMat]
  let mut idx : Std.HashMap (Array Nat) Nat := (Std.HashMap.emptyWithCapacity 200000).insert idPerm 0
  let mut sa : Array Nat := #[]
  let mut sb : Array Nat := #[]
  let mut i : Nat := 0
  while i < perms.size do
    let p := perms[i]!
    let X := mats[i]!
    let qa := p.map fun x => sigmaA[x]!
    let mut ja : Nat := 0
    match idx.get? qa with
    | some j => ja := j
    | none =>
      ja := perms.size
      idx := idx.insert qa ja
      perms := perms.push qa
      mats := mats.push (normMat (mmulArr uCode X))
    sa := sa.push ja
    let qb := p.map fun x => sigmaB[x]!
    let mut jb : Nat := 0
    match idx.get? qb with
    | some j => jb := j
    | none =>
      jb := perms.size
      idx := idx.insert qb jb
      perms := perms.push qb
      mats := mats.push (normMat (mmulArr vCode X))
    sb := sb.push jb
    i := i + 1
  return Table.ofArrays perms mats sa sb

@[expose] def rowsAll (n : Nat) (p : Nat → Bool) : Bool := (List.range n).all p

@[expose] def edgeOK (T : Table) (σ M : Nat → Nat) (s : Nat → Nat) (i : Nat) : Bool :=
  let c := firstNZ (mprod M (T.mat i))
  decide (s i < T.n) && rowsAll 50 (fun x => T.perm (s i) x == σ (T.perm i x)) &&
    decide (0 < c ∧ c < 25) && rowsAll 9 (fun k => fmul c (T.mat (s i) k) == mprod M (T.mat i) k)

@[expose] def rowOK (T : Table) (i : Nat) : Bool :=
  edgeOK T (fun x => sigmaA[x]!) (fun k => uCode[k]!) T.sa i &&
  edgeOK T (fun x => sigmaB[x]!) (fun k => vCode[k]!) T.sb i &&
  rowsAll 9 (fun k => decide (T.mat i k < 25)) && decide (firstNZ (T.mat i) = 1) &&
  (i == 0 || (!rowsAll 50 (fun x => T.perm i x == x) && !rowsAll 9 (fun k => T.mat i k == idCode k)))

@[expose] def rootOK (T : Table) : Bool :=
  decide (0 < T.n) && rowsAll 50 (fun x => T.perm 0 x == x) &&
    rowsAll 9 (fun k => T.mat 0 k == idCode k)

@[expose] def valid (T : Table) : Bool := rootOK T && rowsAll T.n (rowOK T)

end HNUnitaryBridge
