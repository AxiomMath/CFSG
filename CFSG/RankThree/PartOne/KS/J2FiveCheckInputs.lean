module

public import CFSG.RankThree.PartOne.KS.J2FiveData
public import CFSG.Sporadic.SmallOddCore.J2Data
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.J2FiveChains
public import CFSG.RankThree.PartOne.KS.J2FiveCert
public import CFSG.RankThree.PartOne.KS.J2FiveSimp
public import CFSG.RankThree.PartOne.KS.ConjWords
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
public import CFSG.Sporadic.Schreier.PairJ2CheckInputs

public section

namespace CFSG.RankThree.PartOne

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.SmallOddCore
  CFSG.Monster.B.Mathieu CFSG.Sporadic.SmallOddCore.Native

@[expose] def j2FiveKeyPts : List Nat := List.range 8

@[expose] def j2FiveGensR : Array (Array Nat) :=
  #[j2StrongArrs[0]!, j2StrongArrs[1]!, natArr j2OuterTbl]

@[expose] def j2FiveInP (g : Array Nat) : Bool :=
  siftA 315 PairJ2.levels PairJ2.baseArr 0 g

@[expose] def j2FiveInR (g : Array Nat) : Bool :=
  j2FiveInP g || j2FiveInP (compA 315 j2FiveGensR[2]! g)

@[expose] def j2FiveCG (i : Nat) : Array (Array Nat) := j2FiveCGenArrs[i]!

@[expose] def j2FiveDG (i : Nat) : Array (Array Nat) := j2FiveDGenArrs[i]!

@[expose] def j2FiveX (i : Nat) : Array Nat := j2FiveLineArrs[i]!

@[expose] def j2FiveQG (k : Nat) : Array Nat := j2FiveQGenArrs[k]!

@[expose] def j2FiveQCert : ArrCert := j2FiveQLit

@[expose] def j2FiveCCert : Nat → ArrCert
  | 0 => j2FiveCLit0
  | 1 => j2FiveCLit1
  | 2 => j2FiveCLit2
  | 3 => j2FiveCLit3
  | 4 => j2FiveCLit4
  | _ => j2FiveCLit5

@[expose] def j2FiveDCert (i : Nat) : ArrCert :=
  if i = 3 then j2FiveDLit3 else if i = 5 then j2FiveDLit5 else j2FiveDLit2

@[expose] def j2FiveRS (i : Nat) : Array (Array Nat) :=
  #[j2FiveRS0, j2FiveRS1, j2FiveRS2, j2FiveRS3, j2FiveRS4, j2FiveRS5][i]!

@[expose] def j2FiveRW (i : Nat) : Array (List Int) :=
  CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 (j2FiveRS i).size
    #[j2FiveRW0, j2FiveRW1, j2FiveRW2, j2FiveRW3, j2FiveRW4, j2FiveRW5][i]!

@[expose] def j2FiveRBase (i : Nat) : List (Fin 315) :=
  #[j2FiveRBase0, j2FiveRBase1, j2FiveRBase2, j2FiveRBase3, j2FiveRBase4, j2FiveRBase5][i]!

@[expose] def j2FiveRRels (i : Nat) : List (Nat × Nat × Nat) :=
  #[j2FiveRRels0, j2FiveRRels1, j2FiveRRels2, j2FiveRRels3, j2FiveRRels4, j2FiveRRels5][i]!

@[expose] def j2FiveQCheck (c : ArrCert) : Bool :=
  enumOK 315 j2FiveQGenArrs j2FiveKeyPts c && c.pts.size == 25 &&
    allLt 25 (fun k => eqA 315 (powArr 315 c.pts[k]! 5) (idA 315)) &&
    allLt 25 (fun k => eqA 315 c.pts[k]! (idA 315) ||
      (List.range 6).any fun j => (List.range 5).any fun e =>
        eqA 315 c.pts[k]! (powArr 315 (j2FiveX j) e)) &&
    allLt 6 (fun j => allLt 6 fun j' => j == j' ||
      allLt 5 fun e => !(eqA 315 (j2FiveX j) (powArr 315 (j2FiveX j') e))) &&
    allLt 6 (fun j => validA 315 (j2FiveX j) &&
      eqA 315 (powArr 315 (j2FiveX j) 5) (idA 315) &&
      !(eqA 315 (j2FiveX j) (idA 315)) && c.pts.toList.any (eqA 315 (j2FiveX j))) &&
    allLt 2 (fun k => j2FiveInP (j2FiveQG k)) && commA 315 (j2FiveQG 0) (j2FiveQG 1)

@[expose] def j2FiveCentCheck (i N : Nat) : Bool :=
  caseChainOK3 315 (j2FiveRS i) ((j2FiveRBase i).map Fin.val).toArray (j2FiveRW i)
      j2FiveGensR[0]! j2FiveGensR[1]! j2FiveGensR[2]! &&
    centOKP 5 315 (j2FiveRS i) ((j2FiveRBase i).map Fin.val).toArray (j2FiveX i) (j2FiveRRels i)
      (j2FiveCG i) j2FiveKeyPts (j2FiveCCert i) N

@[expose] def j2FiveCPart (i N : Nat) (cC : ArrCert) : Bool :=
  enumOK 315 (j2FiveCG i) j2FiveKeyPts cC && cC.pts.size == N &&
    allLt (j2FiveCG i).size (fun k => commA 315 (j2FiveCG i)[k]! (j2FiveX i)) &&
    allLt (j2FiveCG i).size (fun k => j2FiveInR (j2FiveCG i)[k]!)

@[expose] def j2FiveQPart (N : Nat) (cC cQ : ArrCert) : Bool :=
  allLt 2 (fun k => cC.pts.toList.any (eqA 315 (j2FiveQG k))) &&
    allLt N (fun k => !(commA 315 cC.pts[k]! (j2FiveQG 0) &&
        commA 315 cC.pts[k]! (j2FiveQG 1)) || cQ.pts.toList.any (eqA 315 cC.pts[k]!))

@[expose] def j2FiveGoodCheck (i : Nat) (cC cQ : ArrCert) : Bool :=
  j2FiveCPart i 50 cC && j2FiveQPart 50 cC cQ &&
    allLt (j2FiveCG i).size (fun k => allLt 2 fun l =>
      cQ.pts.toList.any (eqA 315 (conjA 315 (j2FiveCG i)[k]! (j2FiveQG l))))

@[expose] def j2FiveBadCheck (i : Nat) (cC cD cQ : ArrCert) : Bool :=
  j2FiveCPart i 300 cC && j2FiveQPart 300 cC cQ &&
    enumOK 315 (j2FiveDG i) j2FiveKeyPts cD && cD.pts.size == 60 &&
    allLt (j2FiveDG i).size (fun k => cC.pts.toList.any (eqA 315 (j2FiveDG i)[k]!)) &&
    allLt (j2FiveDG i).size (fun k => j2FiveInP (j2FiveDG i)[k]!) &&
    allLt (j2FiveCG i).size (fun k => allLt (j2FiveDG i).size fun l =>
      cD.pts.toList.any (eqA 315 (conjA 315 (j2FiveCG i)[k]! (j2FiveDG i)[l]!))) &&
    (List.range (j2FiveDG i).size).any (fun k => (List.range (j2FiveDG i).size).any
      fun l => !(commA 315 (j2FiveDG i)[k]! (j2FiveDG i)[l]!)) &&
    conjWordsOK 315 cD (j2FiveDG i) (j2FiveSimpSel i) (j2FiveSimpW i) &&
    allLt 300 (fun k => !(allLt (j2FiveDG i).size fun l =>
        commA 315 cC.pts[k]! (j2FiveDG i)[l]!) ||
      (List.range 5).any fun e => eqA 315 cC.pts[k]! (powArr 315 (j2FiveX i) e))

end CFSG.RankThree.PartOne
