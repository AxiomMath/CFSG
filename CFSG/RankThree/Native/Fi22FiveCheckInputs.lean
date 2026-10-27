module

public import CFSG.RankThree.Native.Fi22FiveArrays
public import CFSG.RankThree.Native.ChainCentralizer
public import CFSG.Monster.B.Fischer.Fi22GraphCheck
public meta import CFSG.RankThree.Native.Fi22FiveArrays
public meta import CFSG.RankThree.Native.ChainCentralizer
public meta import CFSG.Monster.B.Fischer.Fi22GraphCheck
public import CFSG.Certificates.NativeSchreierCard
public meta import CFSG.Certificates.NativeSchreierCard
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import Mathlib.GroupTheory.Schreier
public meta import Mathlib.GroupTheory.Schreier
public import Std.Data.HashMap

public section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.Certificates.Native

@[expose] def fi22FiveSiftArrs : List (Array Nat) :=
  [fi22FiveQ1Arr, fi22FiveQ2Arr, compA 3510 fi22GraphOuterArr fi22FiveWArr] ++
    (List.range 6).flatMap fun i =>
      [fi22FiveHArr i, (fi22FiveCGenArrs i)[1]!, (fi22FiveCGenArrs i)[2]!]

@[expose] def fi22FiveX0Pows : List (Array Nat) := (List.range 5).map (powA 3510 fi22FiveQ1Arr)

@[expose] def fi22FiveChainCheck (L : Array Level) : Bool :=
  fi22FiveSiftArrs.all (siftA 3510 L fi22BaseArr 0) &&
    !(siftA 3510 L fi22BaseArr 0 fi22FiveWArr) &&
    fixLevCount 3510 L fi22FiveQ1Arr 0 == 10 && fixLevCount 3510 L fi22FiveQ1Arr 1 == 6 &&
    fixLevCount 3510 L fi22FiveQ1Arr 2 == 2 &&
    tailOK 3510 L fi22FiveQ1Arr fi22FiveX0Pows 3 3 (idA 3510)

@[expose] def fi22FiveLines : Array (Array Nat) := Array.ofFn (n := 6) fun j => fi22FiveLineArr j

@[expose] def fi22FiveQCert : ArrCert := enumBfs 3510 fi22FiveQGenArrs fi22FiveKeyPts 40

@[expose] def fi22FiveQCheck (c : ArrCert) (xs : Array (Array Nat)) : Bool :=
  enumOK 3510 fi22FiveQGenArrs fi22FiveKeyPts c && c.pts.size == 25 &&
    allLt 25 (fun k => eqA 3510 (powA 3510 c.pts[k]! 5) (idA 3510) &&
      allLt 25 fun k' => commA 3510 c.pts[k]! c.pts[k']!) &&
    allLt 25 (fun k => eqA 3510 c.pts[k]! (idA 3510) ||
      (List.range 6).any fun j => (List.range 5).any fun e =>
        eqA 3510 c.pts[k]! (powA 3510 xs[j]! e)) &&
    allLt 6 (fun j => allLt 6 fun j' => j == j' ||
      allLt 5 fun e => !(eqA 3510 xs[j]! (powA 3510 xs[j']! e))) &&
    allLt 6 (fun j => validA 3510 xs[j]! && eqA 3510 (powA 3510 xs[j]! 5) (idA 3510) &&
      !(eqA 3510 xs[j]! (idA 3510)) && c.pts.toList.any (eqA 3510 xs[j]!)) &&
    (fi22FiveQ1Arr[0]! == 0 && fi22FiveQ1Arr[1]! == 1 && fi22FiveQ1Arr[2]! == 2) &&
    validA 3510 fi22FiveWArr && eqA 3510 (compA 3510 fi22FiveWArr fi22FiveWArr) (idA 3510) &&
    !(eqA 3510 fi22FiveWArr (idA 3510))

@[expose] def fi22FiveCCert (i : Nat) : ArrCert :=
  enumBfs 3510 (fi22FiveCGenArrs i) fi22FiveKeyPts 1300

@[expose] def fi22FiveDCert (i : Nat) : ArrCert :=
  enumBfs 3510 (fi22FiveDGenArrs i) fi22FiveKeyPts 80

@[expose] def xwA (x w : Array Nat) (e f : Nat) : Array Nat :=
  compA 3510 (powA 3510 x e) (powA 3510 w f)

@[expose] def orbitFiveCheck (cD : ArrCert) (O : List Nat) : Bool :=
  allLt cD.pts.size fun k => O.all (fun o => O.contains (cD.pts[k]!)[o]!) &&
    (!(O.all fun o => (cD.pts[k]!)[o]! == o) || eqA 3510 cD.pts[k]! (idA 3510))

@[expose] def bWordG (gs : Array (Array Nat)) : Array Nat :=
  compA 3510 gs[1]! (compA 3510 (invCand 3510 gs[2]!) (invCand 3510 gs[2]!))

@[expose] def bWordH (gs : Array (Array Nat)) : Array Nat :=
  compA 3510 (invCand 3510 gs[2]!)
    (compA 3510 (invCand 3510 gs[2]!) (compA 3510 gs[1]! (invCand 3510 gs[2]!)))

@[expose] def fi22FiveRecordCheck (x h : Array Nat) (gs ds : Array (Array Nat)) (cC cD : ArrCert)
    (O : List Nat) : Bool :=
  enumOK 3510 gs fi22FiveKeyPts cC && cC.pts.size == 1200 &&
    enumOK 3510 ds fi22FiveKeyPts cD && cD.pts.size == 60 &&
    allLt 4 (fun k => commA 3510 gs[k]! x) && allLt 4 (fun k => commA 3510 gs[k]! fi22FiveWArr) &&
    eqA 3510 (compA 3510 (bWordG gs) (bWordH gs))
      (compA 3510 gs[2]! (compA 3510 (bWordH gs) (bWordG gs))) &&
    allLt 4 (fun k => allLt 2 fun l => cD.pts.toList.any (eqA 3510 (conjA 3510 gs[k]! ds[l]!))) &&
    allLt 4 (fun k => allLt 4 fun l =>
      cD.pts.toList.any (eqA 3510 (commutatorA 3510 gs[k]! gs[l]!))) &&
    orbitFiveCheck cD O && !(commA 3510 ds[0]! ds[1]!) &&
    allLt 1200 (fun k => !(commA 3510 cC.pts[k]! ds[0]! && commA 3510 cC.pts[k]! ds[1]!) ||
      (List.range 5).any fun e => (List.range 2).any fun f =>
        eqA 3510 cC.pts[k]! (xwA x fi22FiveWArr e f)) &&
    allLt 10 (fun a => allLt 10 fun b => a == b ||
      !(eqA 3510 (xwA x fi22FiveWArr (a % 5) (a / 5)) (xwA x fi22FiveWArr (b % 5) (b / 5)))) &&
    validA 3510 h && eqA 3510 (conjA 3510 h x) fi22FiveQ1Arr && commA 3510 h fi22FiveWArr

@[expose] def fi22FiveRecordOK (i : Nat) : Bool :=
  fi22FiveRecordCheck (fi22FiveLineArr i) (fi22FiveHArr i) (fi22FiveCGenArrs i)
    (fi22FiveDGenArrs i) (fi22FiveCCert i) (fi22FiveDCert i) fi22FiveOrbits[i]!

end CFSG.RankThree.Native
