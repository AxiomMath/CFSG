module

public import Certificates.Data.CFSGNative.Fi23.Slp
public import Certificates.Data.CFSGNative.HN.LevelChain
public import CFSG.Sporadic.Schreier.PairMcLCertInputs

public section

namespace CFSG.Sporadic.PairGen

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.LevelChain.Native

structure PairData where
  words : Array (List Int)
  starts : Array Nat
  base : Array Nat
  sizes : List Nat
  iA : Nat
  iB : Nat
  pa : Nat
  pb : Nat
  pab : Nat

@[expose] def commTab (n : Nat) (P Q : Table) : Bool := compT n P Q == compT n Q P

@[expose] def nestAt (words : Array (List Int)) (starts : Array Nat) (m : Nat) : Bool :=
  allIn 1 m fun i => allIn starts[i]! starts[i + 1]! fun j =>
    words[j]!.all fun z => decide (starts[i - 1]! + 3 ≤ z.natAbs) &&
      decide (z.natAbs < starts[i]! + 3)

@[expose] def pairCheck (n : Nat) (gens : Int → Table) (D : PairData) : Bool :=
  let L := slpLetters n gens D.words
  let m := D.base.size
  let s := D.starts[0]!
  let A := L[2 * D.iA]!
  let B := L[2 * D.iB]!
  let T := levelTrees n L D.starts D.base
  slpOK D.words && L.size == 2 * D.words.size &&
    allIn 0 D.words.size (fun j => invOK n L[2 * j]! L[2 * j + 1]!) &&
    decide (D.iA < D.words.size) && decide (D.iB < D.words.size) &&
    decide (D.pa < n) && decide (D.pb < n) && decide (D.pab < n) &&
    invoOK n A && ap A D.pa != D.pa && invoOK n B && ap B D.pb != D.pb &&
    ap A D.pab != ap B D.pab &&
    commTab n A B && commTab n A L[2 * s]! && commTab n B L[2 * s + 2]! &&
    decide (1 ≤ m) && D.starts.size == m + 1 && D.starts[1]! == s + 2 &&
    D.starts[m]! == D.words.size &&
    allIn 0 m (fun i => decide (D.starts[i]! ≤ D.starts[i + 1]!)) &&
    nestAt D.words D.starts m &&
    allIn 1 m (fun i => allIn D.starts[i]! D.starts[i + 1]! fun j =>
      ap L[2 * j]! D.base[i - 1]! == D.base[i - 1]!) &&
    T.size == m &&
    allIn 0 m (fun i => treeOK n D.base[i]! T[i]! L (levelLv D.starts i)) &&
    orbitSizes T == D.sizes

end CFSG.Sporadic.PairGen

namespace CFSG.Sporadic.McL.Gen45

open CFSG.Sporadic.Th.Native CFSG.Sporadic.PairGen CFSG.Sporadic.Schreier

@[expose] def mclGenWords : Array (List Int) := #[
  [1],
  [-2, -1, -1, -2, -2, -1, -1, 2, -1, -2, -2, -2, 1, 2],
  [1, -4, 1, 4],
  [5, 5, 5],
  [-2, -1, -1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2],
  [3, -7, 3, 7],
  [-1, -2, -1, -1, -2, -1, -1, 2, 2, 2, -1, -2, -2, -1],
  [6, -9, 6, 9],
  [7, 8, 8],
  [9, 10, 10],
  [-11, -12, 11, 12, -11, 12, 11, 12, 11, -12, -12, 11, 11, 11],
  [-11, -11, -11, 12, 11, 12, 11, 12, -11, -11, 12, -11, -11],
  [-14, -13, -13, 14, -13, -14, -13, 14, 13, -14, 13],
  [-13, -14, 13, 13, 14, -13, -13, -14, 13, 13, -14, -13, -13, 14, 13],
  [15, 16, -15, -16, -15, 16, 15, 15],
  [-15, 16, -15, -15, -16, -16, -15, 16, -15, -16, 15, 16, 16],
  [-15, -16, -16, -15, 16, 16, -15, -16, -15],
  [19, -17, -18, -17, 19, -18, 19, 18]
]

@[expose] def mclGenData : PairData where
  words := mclGenWords
  starts := #[8, 10, 12, 14, 17, 18]
  base := #[0, 3, 4, 5, 1]
  sizes := [275, 162, 105, 64, 3]
  iA := 0
  iB := 3
  pa := 1
  pb := 0
  pab := 0

@[expose] def mclGenTbl (k : Nat) : Table := mclStrongArrs[k]!.map UInt32.ofNat

@[expose] def mclLetters (T0 T1 : Table) (z : Int) : Table :=
  if z = 1 then T0 else if z = -1 then invT 275 T0 else if z = 2 then T1 else invT 275 T1

@[expose] def mclGenCheck (T0 T1 : Table) : Bool :=
  invOK 275 T0 (invT 275 T0) && invOK 275 T1 (invT 275 T1) &&
    pairCheck 275 (mclLetters T0 T1) mclGenData

@[expose] def mclGenCertificate (_ : Unit) : Bool :=
  mclGenCheck (mclGenTbl 0) (mclGenTbl 1)

end CFSG.Sporadic.McL.Gen45
