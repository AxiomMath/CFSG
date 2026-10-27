module

public import Std.Data.HashMap

public section

namespace CFSG.D42Over.Native

set_option compiler.extract_closed false

abbrev NMat := Array Nat

@[expose] def mulTab : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 0, 2, 4, 6, 3, 1, 7, 5, 0, 3, 6, 5, 7, 4, 1,
    2, 0, 4, 3, 7, 6, 2, 5, 1, 0, 5, 1, 4, 2, 7, 3, 6, 0, 6, 7, 1, 5, 3, 2, 4, 0, 7, 5, 2, 1, 6,
    4, 3]

@[expose] def gmul (a b : Nat) : Nat := mulTab.getD (8 * (a % 8) + b % 8) 0

@[expose] def nMul (A B : NMat) : NMat :=
  Array.ofFn (n := 64) fun t =>
    let i := t.val / 8
    let j := t.val % 8
    gmul (A.getD (8 * i) 0) (B.getD j 0) ^^^ gmul (A.getD (8 * i + 1) 0) (B.getD (8 + j) 0) ^^^
    gmul (A.getD (8 * i + 2) 0) (B.getD (16 + j) 0) ^^^
    gmul (A.getD (8 * i + 3) 0) (B.getD (24 + j) 0) ^^^
    gmul (A.getD (8 * i + 4) 0) (B.getD (32 + j) 0) ^^^
    gmul (A.getD (8 * i + 5) 0) (B.getD (40 + j) 0) ^^^
    gmul (A.getD (8 * i + 6) 0) (B.getD (48 + j) 0) ^^^
    gmul (A.getD (8 * i + 7) 0) (B.getD (56 + j) 0)

@[expose] def nOne : NMat :=
  #[1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def letters : Array NMat := #[
    #[1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    #[1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0,
      0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    #[1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 6, 5, 0, 0, 0, 0, 0, 1, 0, 6, 0, 0,
      0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1],
    #[1, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 7, 6, 0, 0, 0, 0, 0, 1, 0, 7, 0, 0,
      0, 0, 0, 0, 1, 5, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 1],
    #[1, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 6, 2, 7, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0,
      0, 0, 0, 0, 1, 6, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 1],
    #[1, 5, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 7, 3, 2, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0,
      0, 0, 0, 0, 1, 7, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 0, 0, 0, 0, 0, 0, 0, 1],
    #[1, 6, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 3, 0, 0, 0, 0, 0, 1, 0, 4, 0, 0,
      0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 6, 0, 0, 0, 0, 0, 0, 0, 1],
    #[1, 7, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 5, 4, 0, 0, 0, 0, 0, 1, 0, 5, 0, 0,
      0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 7, 0, 0, 0, 0, 0, 0, 0, 1],
    #[1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    #[1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
      0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    #[1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0,
      0, 0, 6, 0, 1, 0, 0, 0, 0, 0, 5, 6, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1],
    #[1, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 1, 0, 0, 0, 0,
      0, 0, 7, 0, 1, 0, 0, 0, 0, 0, 6, 7, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 1],
    #[1, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 1, 0, 0, 0, 0,
      0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 7, 2, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 1],
    #[1, 0, 0, 0, 0, 0, 0, 0, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 7, 1, 0, 0, 0, 0,
      0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 3, 7, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5, 1],
    #[1, 0, 0, 0, 0, 0, 0, 0, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0,
      0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 3, 4, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 1],
    #[1, 0, 0, 0, 0, 0, 0, 0, 7, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0,
      0, 0, 5, 0, 1, 0, 0, 0, 0, 0, 4, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 7, 1],
    #[1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    #[1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def nLetter (l : Nat) : NMat := letters.getD l (letters.getD 17 nOne)

@[expose] def nWord (w : List Nat) : NMat := w.foldr (fun l A => nMul (nLetter l) A) nOne

@[expose] def nConj (g x g' : NMat) : NMat := nMul (nMul g x) g'

@[expose] def key (A : NMat) : Nat :=
  (A.foldl (fun (h : UInt64) x => (h ^^^ x.toUInt64) * 0x100000001b3) 0xcbf29ce484222325).toNat

@[expose] def evalSyms (gs : Array (NMat × NMat)) (w : List Int) : NMat :=
  w.foldr (fun s A => nMul (if 0 < s then (gs.getD (s.toNat - 1) (nOne, nOne)).1
    else (gs.getD ((-s).toNat - 1) (nOne, nOne)).2) A) nOne

@[expose] def bfs (R S S' : Array NMat) (fuel : Nat) :
    (Array NMat × Array Nat × Array Nat) × Std.HashMap Nat Nat := Id.run do
  let mut list : Array NMat := R
  let mut par : Array Nat := Array.replicate R.size 0
  let mut gen : Array Nat := Array.replicate R.size 0
  let mut seen : Std.HashMap Nat Nat := ∅
  for i in [0:R.size] do
    seen := seen.insert (key (R.getD i nOne)) i
  let mut h := 0
  for _ in [0:fuel] do
    if h < list.size then
      let x := list.getD h nOne
      for j in [0:S.size] do
        let y := nConj (S.getD j nOne) x (S'.getD j nOne)
        let ky := key y
        if !(seen.contains ky) then
          seen := seen.insert ky list.size
          list := list.push y
          par := par.push h
          gen := gen.push j
      h := h + 1
    else
      break
  return ((list, par, gen), seen)

@[expose] def inForest (pts : Array NMat) (idx : Std.HashMap Nat Nat) (n : Nat) (y : NMat) : Bool :=
  match idx[key y]? with
  | some j => j < n && pts.getD j nOne == y
  | none => false

@[expose] def nodeOK (R S S' T T' : Array NMat) (F : Array NMat × Array Nat × Array Nat)
    (idx : Std.HashMap Nat Nat) (n i : Nat) : Bool :=
  let x := F.1.getD i nOne
  (idx[key x]? == some i) &&
  (if i < R.size then x == R.getD i nOne
   else (F.2.1.getD i 0 < i && F.2.2.getD i 0 < S.size &&
     x == nConj (S.getD (F.2.2.getD i 0) nOne) (F.1.getD (F.2.1.getD i 0) nOne)
       (S'.getD (F.2.2.getD i 0) nOne))) &&
  (List.range T.size).all fun l =>
    inForest F.1 idx n (nConj (T.getD l nOne) x (T'.getD l nOne)) &&
    inForest F.1 idx n (nConj (T'.getD l nOne) x (T.getD l nOne))

@[expose] def forestOK (R S S' T T' : Array NMat) (F : Array NMat × Array Nat × Array Nat)
    (idx : Std.HashMap Nat Nat) (n : Nat) : Bool :=
  F.1.size == n && R.size ≤ n && (List.range n).all (nodeOK R S S' T T' F idx n)

end CFSG.D42Over.Native
