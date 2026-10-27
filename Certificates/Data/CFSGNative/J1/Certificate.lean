module

public import Certificates.Data.CFSGNative.J1.Prim

public section

namespace CFSG.Sporadic.J1.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def mA (_ : Unit := ()) : List (List Nat) :=
  [[0, 7, 9, 9, 10, 7, 9], [7, 0, 1, 4, 3, 3, 4], [9, 1, 2, 8, 3, 6, 2], [9, 4, 8, 10, 1, 6, 0],
    [10, 3, 3, 1, 8, 9, 1], [7, 3, 6, 6, 9, 1, 3], [9, 4, 2, 0, 1, 3, 0]]

@[expose] def mB (_ : Unit := ()) : List (List Nat) :=
  [[5, 7, 1, 8, 5, 8, 2], [10, 4, 10, 0, 3, 3, 8], [5, 10, 8, 9, 1, 2, 1], [2, 3, 3, 6, 1, 2, 9],
    [7, 4, 7, 2, 10, 7, 3], [3, 9, 0, 4, 2, 3, 5], [3, 4, 3, 3, 9, 4, 9]]

@[expose] def root (_ : Unit := ()) : List Nat := [1, 2, 7, 7, 2, 9, 10]

@[expose] def chainWords (_ : Unit := ()) : Array (List Int) :=
  #[[1],
    [2],
    [-2, -2, -1, -2, -1, -2, -2, 1, 2, 2, 2, 2, 1, 1, -2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, -2, 1,
      1, 1, 1, 1, -2, -2],
    [-2, -2, 1, -2, 1, -2, -2, 1, 2, 1, 2, 1, 2, 2, 2, 1, -2, 1, 2, 1, 1, 1, 1, -2, -2, 1, 2, 1, 2,
      1, -2, 1, 2, 2, 1, -2, 1, 1, 2, 2],
    [-1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -2,
      -1, -2, -1, -2, -2, -1, 2, 2, 1, -2, 1, -2, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, -2, 1, -2, -2, 1,
      2, 1, 2, 2, 1, 1, 1, 2, 1, -2, 1, -2, 1]]

@[expose] def chainBase : Array Nat := #[0, 1]

@[expose] def chainQ : Array Nat := #[0, 1, 489, 1215, 1116, 269, 759, 2]

@[expose] def chainQb : Array Nat := #[0, 1]

@[expose] def orbitData (_ : Unit) : Orb := orbBFS 11 (sgnKey 11) mA mB root 2000

@[expose] def chainLetters (O : Orb) : Array Table := buildLetters 1540 (genTables O) chainWords

@[expose] def qVecs (O : Orb) : List (List Nat) := chainQ.toList.map fun q => O.pts[q]!

@[expose] def qMat (O : Orb) : List (List Nat) := colMat 7 ((qVecs O).take 7)

@[expose] def actionChecks (O : Orb) (chunks : Nat) : Bool :=
  let L := chainLetters O
  let T := chainTrees 1540 L chainBase
  let P := qMat O
  let Pi := gaussInv 11 7 P
  orbOK 11 7 (pmRel 11) mA mB root O && O.pts.size == 1540 && pmSep 11 7 O.pts chunks &&
    invOK 1540 O.alpha (invT 1540 O.alpha) && invOK 1540 O.beta (invT 1540 O.beta) &&
    chainOK 1540 L chainBase chainQ chainQb T chunks && orbitSizes T == [1540, 114] &&
    wfM 7 P && wfM 7 Pi && mulL 11 7 Pi P == idL 7 &&
    ((mvL 11 Pi ((qVecs O).getD 7 [])).all fun x => x != 0) &&
    primOK 1540 L (levelLetters L chainBase 1) T[0]! (primData 1540 L (levelLetters L chainBase 1) T[0]!)

@[expose] def j1Certificate (chunks : Nat) : Bool := actionChecks (orbitData ()) chunks

end CFSG.Sporadic.J1.Native
