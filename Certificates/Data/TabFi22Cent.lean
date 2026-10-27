module

public import Certificates.Data.K426Checks
public import CFSG.Monster.B.Fischer.PinnedChainInputs
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public import CFSG.RankThree.PartOne.KS.PKit
public meta import Certificates.Data.K426Checks
public meta import CFSG.Monster.B.Fischer.PinnedChainInputs
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public meta import CFSG.RankThree.PartOne.KS.PKit

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi22Cent

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.RankThree.PartTwo.KFacts.K426

@[expose] def hex : String := include_str "TabFi22Cent.txt"

@[expose] def arr (k : ℕ) : Array ℕ := hexTable 3 3510 (3510 * k) hex

@[expose] def dArr (_ : Unit := ()) : Array ℕ := arr 0

@[expose] def xArr (_ : Unit := ()) : Array ℕ := arr 1

@[expose] def lArrs (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 8 => arr (2 + j.val)

@[expose] def lWords : Array (List ℤ) :=
  #[[], [], [-1, -2, -2, 1], [-1, -3, 1, 2], [-1, -2, -1, 2, -3, 2, 3, 1], [3, -4, 5, 5, 3],
    [5, 6, -5], [-3, -6, 5, 4, 3, 4]]

@[expose] def lBase : Array ℕ := [19, 2, 3].toArray

@[expose] def relsU43 : List (List (Fin 2 × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true)],
      [(0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, false), (0, true), (1, false), (0, true), (1, false)],[(0, true), (1, true),
      (1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true),
      (1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true)],
      [(1, true), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false),
      (1, false), (0, true), (1, false), (1, false), (1, false), (0, true), (1, false), (1, false),
      (1, false), (0, true), (1, true), (1, true)],[(0, true), (1, false), (1, false), (0, true),
      (1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (0, true), (1, true),
      (1, true), (0, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, false),
      (0, true), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true),
      (0, true), (1, false)],[(0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
      (1, true), (1, true), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true),
      (1, false), (0, true), (1, false), (1, false), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true),
      (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true),
      (1, true), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, false),
      (1, false)]]

@[expose] def fixCnt (t : Array ℕ) : ℕ := (List.range 3510).countP fun w => t[w]! == w

@[expose] def dxOK (_ : Unit := ()) : Bool :=
  let D := dArr (); let X := xArr ()
  validA 3510 D && validA 3510 X && eqA 3510 (compA 3510 D D) (idA 3510) &&
    eqA 3510 (powArr 3510 X 3) (idA 3510) && !(eqA 3510 X (idA 3510)) &&
    eqA 3510 (compA 3510 (compA 3510 D X) (compA 3510 D X)) (idA 3510)

@[expose] def memOK (_ : Unit := ()) : Bool :=
  let PL := rawLevels 3510 fi22StrongArrs fi22BaseArr
  siftA 3510 PL fi22BaseArr 0 (dArr ()) && siftA 3510 PL fi22BaseArr 0 (xArr ())

@[expose] def genOK (_ : Unit := ()) : Bool :=
  let D := dArr (); let X := xArr ()
  allLt 19 (fun j => let s := fi22StrongArrs[j]!; !(s[0]! == 0) || commA 3510 s D) &&
    allLt 19 (fun j => let s := fi22StrongArrs[j]!
      !(s[0]! == 0 && s[1]! == 1) || commA 3510 s X)

@[expose] def orbitOK (_ : Unit := ()) : Bool :=
  let X := xArr ()
  X[0]! == 1 && !(X[1]! == 0) && !(X[1]! == 1)

@[expose] def invLoopOK (_ : Unit := ()) : Bool :=
  let D := dArr (); let X := xArr ()
  let L0 := (rawLevels 3510 fi22StrongArrs fi22BaseArr)[0]!
  allLt L0.pts.size fun k =>
    let T := L0.tr[k]!
    let Ti := L0.trInv[k]!
    let DY := compA 3510 D (compA 3510 Ti (compA 3510 X T))
    !(eqA 3510 (compA 3510 DY DY) (idA 3510)) ||
      (L0.pts[k]! == 0 || L0.pts[k]! == 1 || L0.pts[k]! == X[1]!)

@[expose] def centCheck (_ : Unit := ()) : Bool :=
  dxOK () && memOK () && genOK () && orbitOK () && invLoopOK ()

@[expose] def lCheck (_ : Unit := ()) : Bool :=
  let S := lArrs ()
  let A := S[0]!; let B := S[1]!
  let X := xArr ()
  let PL := rawLevels 3510 fi22StrongArrs fi22BaseArr
  caseChainOK2P 3510 S lBase lWords A B &&
    decide ((rawOrbitSizes 3510 S lBase).prod = 3265920) &&
    wordsOneOK 3510 #[A, B] relsU43 &&
    siftA 3510 PL fi22BaseArr 0 A && siftA 3510 PL fi22BaseArr 0 B &&
    (A[0]! == 0 && A[1]! == 1 && B[0]! == 0 && B[1]! == 1) &&
    commA 3510 A X && commA 3510 B X

end CFSG.HardMathSupport.Dickson.I271.TabFi22Cent
