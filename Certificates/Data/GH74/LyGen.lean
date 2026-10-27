module

public import Certificates.Data.CFSGNative.Ly.Certificate

public section

namespace CFSG.Sporadic.Ly.Gen

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.LevelChain.Native
  CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Ly.Native

@[expose] def genWords : Array (List Int) := #[
  [2, 2, 2, -1, -2, -2, -2, -2, -2, -2, -2, -1, -2, -1, 2, 2, -1, -2, -1, 2, -1, 2, 2, 2, 2,
     2, -1, -2, 1, 2, 1, -2, -2, -2, -2, -2, 1, -2, 1, 2, 1, -2, -2, 1, 2, 1, 2, 2, 2, 2, 2, 2,
     2, 1, -2, -2, -2, 1],
  [1, 2, 1, -2, -2, -2, -2, -2, 1, -2, 1, 2, 1, -2, -2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 1, -2,
     -2, -2, 1, 3, 3, 3, 3, 3, 3, 3],
  [4, 4],
  [-2, -1, -2, -2, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, 2, 2, -1, -2, -1, 2, -1, -2, -1, -2,
     -2, -2, -2, -2, -2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, -2, 1, 2, 1, -2, -2, 1, 2, 1, -2, 1, -2,
     1, -2, 1, 2, 2, 2, 1, 2, 1],
  [2, 2, 2, 2, 2, 2, 1, 2, 1, -2, 1, 2, 1, -2, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 2, 2, 1,
     2, 1, 6, 6, 6, 6],
  [-2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, -2, -2, 1, -2, -2, 1, -2, -2, -2, -2, 1, 2,
     1, -2, 1, -2, -2, -2, 1, -2, -2, -2, 1, -2, -1, 2, -1, 2, 2, 2, -1, 2, 2, 2, -1, 2, -1, -2,
     -1, 2, 2, 2, 2, -1, 2, 2, -1, 2, 2, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -2, -2, -1,
     2],
  [-7, -8, 7, 7, 7, 7, -8, -7, -8, -7, -8, 7, 8, -7, 8, -7, 8, -7, -7, 8, -7, 8, -7, 8, -7],
  [-7, -7, -8, -7, -8, -7, -8, 7, -8, -7, -8, 7, -8, 7, 8, 7, 7, 7, 8, -7, 8, 7, 8, -7, 8, 7],
  [7, -8, -7, -8, 7, 7, -8, 7, 7, -8, 7, -8, -7, -7, -8, -7, 8, -7, 8, -7, -7, -7, -7, -7, 8,
     7, 8, 7, 7],
  [7, -8, 7, 7, 7, 7, 7, 7, -8, 7, 7, 7, 7, 7, 7, 7, 7, 8, 7, 8, 7, 7, 8, 7, 8, 7, 8, 7],
  [-11, -9, -12, -10, -11, -9, 12, -9, -10, 11, 12],
  [9, -12, 9, 12, 11, 11, 12, -9, 10, 11, -9, 10],
  [-9, -10, 9, -10, 11, -12, 11, 11, -10, -9, -10, -9],
  [12, -9, 12, 9, 11, 10, 12, -11, 9, 9, 10],
  [-11, 9, 11, 10, -12, -12, -11, 12, -10, -10, 9, -11]
]

@[expose] def genStarts : Array Nat := #[4, 6, 10, 15]

@[expose] def genBase : Array Nat := #[0, 3, 1]

@[expose] def genSizes : List Nat := [8835156, 2034375, 2880]

@[expose] def genPt : Nat := 0

@[expose] def genTablesI (alpha beta betaI : Table) (z : Int) : Table :=
  if z = 1 ∨ z = -1 then alpha else if z = 2 then beta else betaI

@[expose] def genLetters (alpha beta : Table) : Array Table :=
  slpLetters nPts (genTablesI alpha beta (invT nPts beta)) genWords

@[expose] def commT (P Q : Table) : Bool := compT nPts P Q == compT nPts Q P

@[expose] def genNest : Bool :=
  allIn 1 3 fun i => allIn genStarts[i]! genStarts[i + 1]! fun j =>
    genWords[j]!.all fun z => decide (genStarts[i - 1]! + 3 ≤ z.natAbs) &&
      decide (z.natAbs < genStarts[i]! + 3)

@[expose] def genCheck (alpha beta : Table) : Bool :=
  let L := genLetters alpha beta
  let U := L[4]!
  let U7 := powT nPts 7 U
  let U3 := powT nPts 3 U
  let T := levelTrees nPts L genStarts genBase
  slpOK genWords && genWords.size == 15 && L.size == 30 &&
    allIn 0 genWords.size (fun j => invOK nPts L[2 * j]! L[2 * j + 1]!) &&
    commT alpha U && commT alpha L[8]! && commT U7 L[10]! &&
    order3OK nPts U7 && ap U7 genPt != genPt && ap U3 genPt != genPt &&
    genNest &&
    allIn 1 3 (fun i => allIn genStarts[i]! genStarts[i + 1]! fun j =>
      ap L[2 * j]! genBase[i - 1]! == genBase[i - 1]!) &&
    T.size == 3 &&
    allIn 0 3 (fun i => treeOK nPts genBase[i]! T[i]! L (levelLv genStarts i)) &&
    orbitSizes T == genSizes

@[expose] def genCertificate (_ : Unit) : Bool :=
  let O := orbitData ()
  genCheck O.alpha O.beta

end CFSG.Sporadic.Ly.Gen
