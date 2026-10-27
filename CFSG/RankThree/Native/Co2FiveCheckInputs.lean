module

public import CFSG.RankThree.Native.Co2FiveArrays
public import CFSG.RankThree.Native.ChainCentralizer
public import CFSG.Sporadic.Co2Cert.OrderCheck
public meta import CFSG.RankThree.Native.Co2FiveArrays
public meta import CFSG.RankThree.Native.ChainCentralizer
public meta import CFSG.Sporadic.Co2Cert.OrderCheck
public meta import CFSG.Certificates.NativeSchreierCard
public import CFSG.Certificates.NativeSchreierCard

public section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Co2Cert
  CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer

@[expose] def co2FiveC0Cert : ArrCert := enumBfs 2300 co2FiveC0GenArrs co2FiveKeyPts 3100

@[expose] def co2FiveQCert : ArrCert := enumBfs 2300 co2FiveQGenArrs co2FiveKeyPts 130

@[expose] def co2FiveC1Cert : ArrCert := enumBfs 2300 co2FiveC1GenArrs co2FiveKeyPts 700

@[expose] def co2FiveDCert : ArrCert := enumBfs 2300 co2FiveDGenArrs co2FiveKeyPts 70

@[expose] def co2FiveSiftArrs : List (Array Nat) :=
  [co2FiveX0Arr, co2FiveX1Arr, co2FiveTArr] ++ co2FiveC0GenArrs.toList ++
    co2FiveQGenArrs.toList ++ co2FiveC1GenArrs.toList ++ (List.range 31).map co2FiveHArr

@[expose] def co2FiveZPows : List (Array Nat) := (List.range 5).map (powArr 2300 co2FiveZArr)

@[expose] def co2FiveX0PowArrs : Array (Array Nat) :=
  Array.ofFn (n := 5) fun e => powArr 2300 co2FiveX0Arr e

@[expose] def co2FiveChainCheck (L : Array Level) (cC0 : ArrCert) : Bool :=
  co2FiveSiftArrs.all (siftA 2300 L co2BaseArr 0) &&
    (co2FiveZArr[0]! == 0 && co2FiveZArr[1]! == 1 && co2FiveZArr[2]! == 2 &&
      co2FiveZArr[3]! == 3) &&
    fixLevCount 2300 L co2FiveZArr 0 == 10 && fixLevCount 2300 L co2FiveZArr 1 == 3 &&
    fixLevCount 2300 L co2FiveZArr 2 == 2 && fixLevCount 2300 L co2FiveZArr 3 == 2 &&
    tailOK 2300 L co2FiveZArr co2FiveZPows 2 4 (idA 2300) &&
    co2FiveRels.all (fun r => decide (r.2.2 < co2FiveX0PowArrs.size) &&
      decide (r.1 < co2BaseArr.size) && decide (r.2.1 < co2BaseArr.size) &&
      (co2FiveX0PowArrs[r.2.2]!)[co2BaseArr[r.1]!]! == co2BaseArr[r.2.1]!) &&
    ptailOK 2300 L co2BaseArr co2FiveX0Arr co2FiveX0PowArrs co2FiveRels cC0.pts.toList 6 0
      (idA 2300)

@[expose] def co2FiveLines : Array (Array Nat) := Array.ofFn (n := 31) fun j => co2FiveLineArr j

@[expose] def co2FiveQCheck (c : ArrCert) (xs : Array (Array Nat)) : Bool :=
  enumOK 2300 co2FiveQGenArrs co2FiveKeyPts c && c.pts.size == 125 &&
    allLt 125 (fun k => eqA 2300 (powArr 2300 c.pts[k]! 5) (idA 2300)) &&
    allLt 125 (fun k => eqA 2300 c.pts[k]! (idA 2300) ||
      (List.range 31).any fun j => (List.range 5).any fun e =>
        eqA 2300 c.pts[k]! (powArr 2300 xs[j]! e)) &&
    allLt 31 (fun j => allLt 31 fun j' => j == j' ||
      allLt 5 fun e => !(eqA 2300 xs[j]! (powArr 2300 xs[j']! e))) &&
    allLt 31 (fun j => validA 2300 xs[j]! && eqA 2300 (powArr 2300 xs[j]! 5) (idA 2300) &&
      !(eqA 2300 xs[j]! (idA 2300)) && c.pts.toList.any (eqA 2300 xs[j]!)) &&
    allLt 31 (fun j => validA 2300 (co2FiveHArr j))

@[expose] def co2FiveC0Check (cC0 cA : ArrCert) : Bool :=
  enumOK 2300 co2FiveC0GenArrs co2FiveKeyPts cC0 && cC0.pts.size == 3000 &&
    allLt 2 (fun k => commA 2300 co2FiveC0GenArrs[k]! co2FiveX0Arr) &&
    allLt 2 (fun k => cC0.pts.toList.any (eqA 2300 co2FiveAGenArrs[k]!)) &&
    allLt 2 (fun k => allLt 2 fun l =>
      cA.pts.toList.any (eqA 2300 (conjA 2300 co2FiveC0GenArrs[k]! co2FiveAGenArrs[l]!))) &&
    allLt 3000 (fun k => !(commA 2300 cC0.pts[k]! co2FiveAGenArrs[0]! &&
        commA 2300 cC0.pts[k]! co2FiveAGenArrs[1]!) ||
      (List.range 5).any fun e => eqA 2300 cC0.pts[k]! (powArr 2300 co2FiveX0Arr e))

@[expose] def co2BWordG (gs : Array (Array Nat)) : Array Nat :=
  compA 2300 gs[1]! (compA 2300 (invCand 2300 gs[2]!) (invCand 2300 gs[2]!))

@[expose] def co2BWordH (gs : Array (Array Nat)) : Array Nat :=
  compA 2300 gs[1]! (compA 2300 gs[2]! (compA 2300 gs[1]! gs[2]!))

@[expose] def co2FiveC1Check (gs ds : Array (Array Nat)) (cC1 cD : ArrCert) : Bool :=
  enumOK 2300 gs co2FiveKeyPts cC1 && cC1.pts.size == 600 &&
    enumOK 2300 ds co2FiveKeyPts cD && cD.pts.size == 60 &&
    allLt 3 (fun k => commA 2300 gs[k]! co2FiveX1Arr) &&
    eqA 2300 (compA 2300 (co2BWordG gs) (co2BWordH gs))
      (compA 2300 gs[2]! (compA 2300 (co2BWordH gs) (co2BWordG gs))) &&
    allLt 3 (fun k => allLt 2 fun l => cD.pts.toList.any (eqA 2300 (conjA 2300 gs[k]! ds[l]!))) &&
    allLt 3 (fun k => allLt 3 fun l =>
      cD.pts.toList.any (eqA 2300 (commutatorA 2300 gs[k]! gs[l]!))) &&
    !(commA 2300 ds[0]! ds[1]!) && conjSimpleOK 2300 co2FiveKeyPts cD &&
    allLt 600 (fun k => !(commA 2300 cC1.pts[k]! ds[0]! && commA 2300 cC1.pts[k]! ds[1]!) ||
      (List.range 5).any fun e => eqA 2300 cC1.pts[k]! (powArr 2300 co2FiveX1Arr e)) &&
    validA 2300 co2FiveTArr

end CFSG.RankThree.Native
