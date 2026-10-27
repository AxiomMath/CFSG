module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeInputs
public import Certificates.Data.K426Checks
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2Kit
public import Certificates.Data.U42Presentation
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeInputs
public meta import Certificates.Data.K426Checks
public meta import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2Kit
public meta import Certificates.Data.U42Presentation

public section

namespace CFSG.HardMathSupport.Dickson.I271.Co2Cent

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Co2Cert
  CFSG.RankThree.PartTwo.KFacts.K426 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.U42Presentation

@[expose] def co2Hex : String := include_str "Co2Cent.txt"

@[expose] def co2Arr (k : ℕ) : Array ℕ := hexTable 3 2300 (2300 * k) co2Hex

@[expose] def co2ChainAArrs (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 16 => co2Arr (0 + j.val)

@[expose] def co2ChainAWords : Array (List ℤ) :=
  #[[], [], [2, 1, 2], [-1, -3], [-1, -4, -4, -3, 4, 1], [-5, -4, -5, 4, 4, 5, -4, -4, 5, 4], [4, 4, -5, 6, -4, -4], [4, 4, 7, -4, -4], [4, 4, 8, -4, -4], [-7, -6, -8, 9, 6, 7], [-6, 10, 6], [-7, -6, -4, -5, -8, 11, 5, 4], [-4, -4, -6, 4, 9, 4], [-5, -7, -11, -13, -4, -5, -4, 8, -12, 4], [-5, -8, -9, -12, -13, -4, -9, -5, 13, 6, -4], [-13, 15, 13]]

@[expose] def co2ChainABase : Array ℕ :=
  [0, 1, 747, 956, 1664, 2, 1868, 2254, 3, 4].toArray

@[expose] def co2RelsA : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 1), (0, 0, 2), (1, 1, 1), (1, 1, 2), (2, 2, 1), (2, 2, 2), (3, 3, 1), (3, 3, 2), (4, 4, 1), (4, 4, 2), (5, 6, 1), (5, 7, 2), (6, 7, 1), (6, 5, 2), (7, 5, 1), (7, 6, 2)]

@[expose] def co2RGens (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 4 => co2Arr (33 + j.val)

@[expose] def co2RKeys : List ℕ := [6]

@[expose] def co2RCert (_ : Unit := ()) : ArrCert := enumBfs 2300 (co2RGens ()) co2RKeys 250

@[expose] def co2ChainBArrs (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 17 => co2Arr (16 + j.val)

@[expose] def co2ChainBWords : Array (List ℤ) :=
  #[[], [], [2, 1, 2], [-1, -3], [-1, -4, -4, -3, 4, 1], [4, 5, -4], [-4, -5, 6, 5, 4], [-4, 7, 4], [-6, 8, 6], [-7, 9, 7], [-5, 4, 9, -4, 5], [-4, -8, 11, 8, 4], [-6, -10, 12, 10, 6], [-6, -11, -7, 12, 7, 11, 6], [-4, 12, 4], [-6, 15, 6], [-12, -14, -5, -9, -4, -4, 11, -4]]

@[expose] def co2ChainBBase : Array ℕ :=
  [0, 1, 16, 28, 67, 106, 2].toArray

@[expose] def co2RelsB : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 1), (0, 0, 2), (1, 1, 1), (1, 1, 2), (2, 2, 1), (2, 2, 2), (3, 3, 1), (3, 3, 2), (4, 4, 1), (4, 4, 2), (5, 5, 1), (5, 5, 2)]

@[expose] def co2LArrs (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 6 => co2Arr (37 + j.val)

@[expose] def co2LGens (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 2 => co2Arr (37 + j.val)

@[expose] def co2LWords : Array (List ℤ) :=
  #[[], [], [-2, 1, 2], [2, -1, -2, -2], [-3, -4, -3, 4, -3, -4, -1, -2, 3, 2, 1], [-3, -4, -4, -5, 4, 3, 4, 4]]

@[expose] def co2LBase : Array ℕ :=
  [0, 2, 3].toArray

@[expose] def co2FusConj (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 40 => co2Arr (43 + j.val)

@[expose] def co2FusIdx : Array ℕ :=
  #[0, 0, 0, 1, 2, 3, 1, 3, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 4, 6, 5, 10, 12, 11, 7, 9, 8, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 13, 15, 14, 19, 21, 20, 16, 18, 17, 31, 33, 32, 37, 39, 38, 34, 36, 35, 22, 24, 23, 28, 30, 29, 25, 27, 26]

@[expose] def co2FusCls : Array ℕ :=
  #[0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1]

@[expose] def co2FusExp : Array ℕ :=
  #[1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]

@[expose] def co2CaseACheck (_ : Unit := ()) : Bool :=
  caseChainOK2P 2300 (co2ChainAArrs ()) co2ChainABase co2ChainAWords co2OrigArrs[0]! co2OrigArrs[1]! &&
    centNormOKP 3 2300 (co2ChainAArrs ()) co2ChainABase (dElts ())[3]! co2RelsA (co2RGens ())
      co2RKeys (co2RCert ()) 243 &&
    validA 2300 (dElts ())[3]! && eqA 2300 (powArr 2300 (dElts ())[3]! 3) (idA 2300) &&
    !(eqA 2300 (dElts ())[3]! (idA 2300))

@[expose] def co2CaseBCheck (_ : Unit := ()) : Bool :=
  let LL := rawLevels 2300 (co2LArrs ()) co2LBase
  caseChainOK2P 2300 (co2ChainBArrs ()) co2ChainBBase co2ChainBWords co2OrigArrs[0]! co2OrigArrs[1]! &&
    caseChainOK2P 2300 (co2LArrs ()) co2LBase co2LWords (co2LGens ())[0]! (co2LGens ())[1]! &&
    (rawOrbitSizes 2300 (co2LArrs ()) co2LBase).prod == 25920 &&
    centNormMemOKP 3 2300 (co2ChainBArrs ()) co2ChainBBase (dElts ())[1]! co2RelsB (co2LGens ())
      (fun t => siftA 2300 LL co2LBase 0 t) (fun t => eqA 2300 (powArr 2300 t 3) (idA 2300)) &&
    validA 2300 (dElts ())[1]! && eqA 2300 (powArr 2300 (dElts ())[1]! 3) (idA 2300) &&
    !(eqA 2300 (dElts ())[1]! (idA 2300)) &&
    wordsOneOK 2300 (co2LGens ()) u42Words

@[expose] def co2FusCheck (_ : Unit := ()) : Bool :=
  let L := levels ()
  let E := dElts ()
  let H := co2FusConj ()
  let XA := E[3]!
  let XB := E[1]!
  H.size == 40 && co2FusIdx.size == 81 && co2FusCls.size == 81 && co2FusExp.size == 81 &&
    E.size == 81 &&
    allLt 40 (fun j => validA 2300 H[j]! && inP L H[j]!) &&
    allLt 81 (fun k => k == 0 || (decide (co2FusIdx[k]! < 40) && decide (co2FusCls[k]! < 2) &&
      decide (1 ≤ co2FusExp[k]! ∧ co2FusExp[k]! ≤ 2) &&
      eqA 2300 (conjA 2300 H[co2FusIdx[k]!]! E[k]!)
        (powArr 2300 (if co2FusCls[k]! == 0 then XA else XB) co2FusExp[k]!)))

end CFSG.HardMathSupport.Dickson.I271.Co2Cent
