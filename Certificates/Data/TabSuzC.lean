module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThreeInputs
public import Certificates.Data.K426J3
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThreeInputs
public meta import Certificates.Data.K426J3

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabSuzC

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
  CFSG.RankThree.PartTwo.KFacts.K426
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT

@[expose] def aTuples : Array (Array Nat) :=
  #[#[89, 1324, 270, 1173, 1010, 1003], #[87, 1039, 1570, 1162, 781, 765]]

@[expose] def sTuples : Array (Array Nat) :=
  #[#[813, 1580, 797, 168, 1434, 632], #[115, 1777, 1049, 415, 1741, 632]]

@[expose] def tTuple : Array Nat := #[15, 543, 95, 1058, 1309, 1759]

@[expose] def aGens (L : Array Level) : Array (Array Nat) := aTuples.map (rebuild L)

@[expose] def aCert (L : Array Level) : ArrCert := enumBfs 1782 (aGens L) cKeys 400

@[expose] def sGens (L : Array Level) : Array (Array Nat) := sTuples.map (rebuild L)

@[expose] def sCert (L : Array Level) : ArrCert := enumBfs 1782 (sGens L) cKeys 12

@[expose] def tArr (L : Array Level) : Array Nat := rebuild L tTuple

@[expose] def tabSuzCCheck (_ : Unit := ()) : Bool :=
  let L := levels ()
  let y := yArr L
  let ag := aGens L
  let ac := aCert L
  let sg := sGens L
  let sc := sCert L
  let t := tArr L
  derivedLeOK 1782 (cGens L) ag cKeys ac 360 &&
    allLt ag.size (fun l => inP L ag[l]! && commA 1782 ag[l]! y) &&
    wordsOneOK 1782 ag j3tLiftRels &&
    enumOK 1782 sg cKeys sc && sc.pts.size == 9 &&
    allLt sg.size (fun l => ac.pts.toList.any (eqA 1782 sg[l]!)) &&
    commA 1782 sg[0]! sg[1]! &&
    allLt sg.size (fun l => eqA 1782 (powArr 1782 sg[l]! 3) (idA 1782)) &&
    validA 1782 t && inP L t &&
    allLt ag.size (fun l => ac.pts.toList.any (eqA 1782 (conjA 1782 t ag[l]!)) &&
      ac.pts.toList.any (eqA 1782 (conjInvA 1782 t ag[l]!))) &&
    eqA 1782 (conjA 1782 t sg[0]!) sg[0]! &&
    eqA 1782 (conjA 1782 t sg[1]!) (powArr 1782 sg[1]! 2)

end CFSG.HardMathSupport.Dickson.I271.TabSuzC
