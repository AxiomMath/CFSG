module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeInputs
public import Certificates.Data.K426Checks
public import Certificates.Data.Co3Pump
public import CFSG.RankThree.PartOne.KS.PKitLeaf
public import Certificates.Data.L28Presentation
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeInputs
public meta import Certificates.Data.K426Checks
public meta import Certificates.Data.Co3Pump
public meta import CFSG.RankThree.PartOne.KS.PKitLeaf
public meta import Certificates.Data.L28Presentation

public section

namespace CFSG.HardMathSupport.Dickson.I271.Co3Cent

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Sporadic.Schreier.Co3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T
  CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump
  CFSG.HardMathSupport.Dickson.I271.L28Presentation

@[expose] def hex : String := include_str "Co3Cent.txt"

@[expose] def arr (k : ℕ) : Array ℕ := hexTable 3 276 (276 * k) hex

@[expose] def chainBArrs (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 14 => arr (0 + j.val)

@[expose] def chainBWords : Array (List ℤ) :=
  #[[], [], [-2, -1, -2, -2, 1, 2], [1, 3, -1], [-3, -4, -1, -3, 4, -1, 4, 3],
    [-1, -3, -4, -3, -2, -2, 3, 2, 2], [-6, -6], [-6, 4, 6], [-8, -7, -7, 8], [-7, -8, 7, 8, 7, 8],
    [-4, 10, 4], [-10, 11, -7, -7, -11], [-9, -12],
    [-8, 11, 12, -4, 7, 13, -3, -4, -6, -2, -4, -2, 3, 2]]

@[expose] def chainBBaseArr : Array ℕ :=
  [0, 21, 43, 47, 88, 105, 162, 198, 214, 216, 233, 241, 246, 262, 268, 1, 263].toArray

@[expose] def relsB : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 1), (0, 0, 2), (1, 1, 1), (1, 1, 2), (2, 2, 1), (2, 2, 2), (3, 3, 1), (3, 3, 2),
    (4, 4, 1), (4, 4, 2), (5, 5, 1), (5, 5, 2), (6, 6, 1), (6, 6, 2), (7, 7, 1), (7, 7, 2),
    (8, 8, 1), (8, 8, 2), (9, 9, 1), (9, 9, 2), (10, 10, 1), (10, 10, 2), (11, 11, 1), (11, 11, 2),
    (12, 12, 1), (12, 12, 2), (13, 13, 1), (13, 13, 2), (14, 14, 1), (14, 14, 2), (15, 16, 1),
    (16, 15, 2)]

@[expose] def chainAArrs (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 17 => arr (14 + j.val)

@[expose] def chainAWords : Array (List ℤ) :=
  #[[], [], [-2, -2], [1, 2, 1, -2, -1], [-4, -3, -4, 3, 4, 3, 4], [-3, 5, 3], [-1, -2, 6, 2, 1],
    [-7, -3, 7, 3, 7], [-4, -5, 8, 5, 4], [-5, -9, -6, 8, 9, 5], [-6, 10, 6], [-10, -8, 11, 8, 6],
    [12, 11, 8], [-11, -8, -11, -10, -8, -10, 13, 11, 10], [-11, 14, -3, 13, 3],
    [-6, -8, 10, 15, 8, 10], [12, -16, -10, -11, -5, -6, -4, -9, -10, -1, 12, -4, 2]]

@[expose] def chainABaseArr : Array ℕ :=
  [2, 47, 88, 162, 252, 267, 0, 246, 262, 1, 3].toArray

@[expose] def relsA : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 1), (0, 0, 2), (1, 1, 1), (1, 1, 2), (2, 2, 1), (2, 2, 2), (3, 3, 1), (3, 3, 2),
    (4, 4, 1), (4, 4, 2), (5, 5, 1), (5, 5, 2), (6, 7, 1), (6, 8, 2), (7, 8, 1), (7, 6, 2),
    (8, 6, 1), (8, 7, 2)]

@[expose] def rGens (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 5 => arr (31 + j.val)

@[expose] def lGens (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 2 => arr (36 + j.val)


@[expose] def dCert (_ : Unit := ()) : ArrCert := enumBfs 276 (dGens ()) keys 250

@[expose] def rCert (_ : Unit := ()) : ArrCert := enumBfs 276 (rGens ()) keys 250

@[expose] def lCert (_ : Unit := ()) : ArrCert := enumBfs 276 (lGens ()) keys 520

@[expose] def caseBCheck (_ : Unit := ()) : Bool :=
  caseChainOK2P 276 (chainBArrs ()) chainBBaseArr chainBWords co3ChainArrs[0]! co3ChainArrs[1]! &&
    centNormOKP 3 276 (chainBArrs ()) chainBBaseArr (dElts ())[kB]! relsB (dGens ()) keys
      (dCert ()) 243 &&
    validA 276 (dElts ())[kB]! && eqA 276 (powArr 276 (dElts ())[kB]! 3) (idA 276) &&
    !(eqA 276 (dElts ())[kB]! (idA 276))

@[expose] def caseACheck (_ : Unit := ()) : Bool :=
  caseChainOK2P 276 (chainAArrs ()) chainABaseArr chainAWords co3ChainArrs[0]! co3ChainArrs[1]! &&
    centNormOKP 3 276 (chainAArrs ()) chainABaseArr (dElts ())[kA]! relsA (rGens ()) keys
      (rCert ()) 243 &&
    validA 276 (dElts ())[kA]! && eqA 276 (powArr 276 (dElts ())[kA]! 3) (idA 276) &&
    !(eqA 276 (dElts ())[kA]! (idA 276))

@[expose] def caseCCheck (_ : Unit := ()) : Bool :=
  derivedLeOK 276 (cGens ()) (lGens ()) keys (lCert ()) 504 &&
    allLt (lGens ()).size (fun l => (cCert ()).pts.toList.any (eqA 276 (lGens ())[l]!)) &&
    wordsOneOK 276 (lGens ()) l28Words

end CFSG.HardMathSupport.Dickson.I271.Co3Cent
