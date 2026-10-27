module

public import CFSG.RankThree.Native.Co3FiveArrays
public import CFSG.RankThree.Native.ChainCentralizer
public import CFSG.Sporadic.Schreier.Co3OrderCheck
public import CFSG.Monster.B.Mathieu.SylowCore
public meta import CFSG.RankThree.Native.Co3FiveArrays
public meta import CFSG.RankThree.Native.ChainCentralizer
public meta import CFSG.Sporadic.Schreier.Co3OrderCheck
public meta import CFSG.Monster.B.Mathieu.SylowCore
public meta import CFSG.Certificates.NativeSchreierCard
public import CFSG.Certificates.NativeSchreierCard
public import Std.Data.HashMap

public section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer

@[expose] def co3FiveC25Cert : ArrCert := enumBfs 276 co3FiveC25GenArrs co3FiveKeyPts 1600

@[expose] def co3FiveQCert : ArrCert := enumBfs 276 co3FiveQGenArrs co3FiveKeyPts 130

@[expose] def co3FiveC0Cert : ArrCert := enumBfs 276 co3FiveC0GenArrs co3FiveKeyPts 400

@[expose] def co3FiveDCert : ArrCert := enumBfs 276 co3FiveDGenArrs co3FiveKeyPts 70

@[expose] def co3FiveSiftArrs : List (Array Nat) :=
  [co3FiveX0Arr, co3FiveX25Arr, co3FiveTArr, co3FiveGArr, co3FiveKArr] ++
    co3FiveC25GenArrs.toList ++ co3FiveQGenArrs.toList ++ co3FiveC0GenArrs.toList ++
    (List.range 31).map co3FiveHArr

@[expose] def co3FiveZPows : List (Array Nat) := (List.range 5).map (powArr 276 co3FiveZArr)

@[expose] def co3FiveX25PowArrs : Array (Array Nat) :=
  Array.ofFn (n := 5) fun e => powArr 276 co3FiveX25Arr e

@[expose] def co3FiveChainCheck (L : Array Level) (cC25 : ArrCert) : Bool :=
  co3FiveSiftArrs.all (siftA 276 L co3ChainBaseArr 0) &&
    (co3FiveZArr[0]! == 0 && co3FiveZArr[1]! == 1 && co3FiveZArr[2]! == 2 &&
      co3FiveZArr[3]! == 3) &&
    fixLevCount 276 L co3FiveZArr 0 == 6 && fixLevCount 276 L co3FiveZArr 1 == 5 &&
    fixLevCount 276 L co3FiveZArr 2 == 2 && fixLevCount 276 L co3FiveZArr 3 == 1 &&
    tailOK 276 L co3FiveZArr co3FiveZPows 3 4 (idA 276) &&
    co3FiveRels.all (fun r => decide (r.2.2 < co3FiveX25PowArrs.size) &&
      decide (r.1 < co3ChainBaseArr.size) && decide (r.2.1 < co3ChainBaseArr.size) &&
      (co3FiveX25PowArrs[r.2.2]!)[co3ChainBaseArr[r.1]!]! == co3ChainBaseArr[r.2.1]!) &&
    ptailOK 276 L co3ChainBaseArr co3FiveX25Arr co3FiveX25PowArrs co3FiveRels cC25.pts.toList 7
      0 (idA 276)

@[expose] def co3FiveLines : Array (Array Nat) := Array.ofFn (n := 31) fun j => co3FiveLineArr j

@[expose] def co3FiveQCheck (c : ArrCert) (xs : Array (Array Nat)) : Bool :=
  enumOK 276 co3FiveQGenArrs co3FiveKeyPts c && c.pts.size == 125 &&
    allLt 125 (fun k => eqA 276 (powArr 276 c.pts[k]! 5) (idA 276)) &&
    allLt 125 (fun k => eqA 276 c.pts[k]! (idA 276) ||
      (List.range 31).any fun j => (List.range 5).any fun e =>
        eqA 276 c.pts[k]! (powArr 276 xs[j]! e)) &&
    allLt 31 (fun j => allLt 31 fun j' => j == j' ||
      allLt 5 fun e => !(eqA 276 xs[j]! (powArr 276 xs[j']! e))) &&
    allLt 31 (fun j => validA 276 xs[j]! && eqA 276 (powArr 276 xs[j]! 5) (idA 276) &&
      !(eqA 276 xs[j]! (idA 276)) && c.pts.toList.any (eqA 276 xs[j]!)) &&
    allLt 31 (fun j => validA 276 (co3FiveHArr j))

@[expose] def co3FiveC25Check (cC25 cA : ArrCert) : Bool :=
  enumOK 276 co3FiveC25GenArrs co3FiveKeyPts cC25 && cC25.pts.size == 1500 &&
    allLt 4 (fun k => commA 276 co3FiveC25GenArrs[k]! co3FiveX25Arr) &&
    allLt 2 (fun k => cC25.pts.toList.any (eqA 276 co3FiveAGenArrs[k]!)) &&
    allLt 4 (fun k => allLt 2 fun l =>
      cA.pts.toList.any (eqA 276 (conjA 276 co3FiveC25GenArrs[k]! co3FiveAGenArrs[l]!))) &&
    allLt 1500 (fun k => !(commA 276 cC25.pts[k]! co3FiveAGenArrs[0]! &&
        commA 276 cC25.pts[k]! co3FiveAGenArrs[1]!) ||
      (List.range 5).any fun e => eqA 276 cC25.pts[k]! (powArr 276 co3FiveX25Arr e))

@[expose] def co3FiveC0Check (gs ds : Array (Array Nat)) (cC0 cD : ArrCert) : Bool :=
  enumOK 276 gs co3FiveKeyPts cC0 && cC0.pts.size == 300 &&
    enumOK 276 ds co3FiveKeyPts cD && cD.pts.size == 60 &&
    allLt 3 (fun k => commA 276 gs[k]! co3FiveX0Arr) &&
    validA 276 co3FiveGArr && validA 276 co3FiveKArr &&
    cC0.pts.toList.any (eqA 276 co3FiveGArr) && cC0.pts.toList.any (eqA 276 co3FiveKArr) &&
    eqA 276 gs[2]! (commutatorA 276 co3FiveGArr co3FiveKArr) &&
    allLt 3 (fun k => allLt 2 fun l => cD.pts.toList.any (eqA 276 (conjA 276 gs[k]! ds[l]!))) &&
    allLt 3 (fun k => allLt 3 fun l =>
      cD.pts.toList.any (eqA 276 (commutatorA 276 gs[k]! gs[l]!))) &&
    !(commA 276 ds[0]! ds[1]!) && conjSimpleOK 276 co3FiveKeyPts cD &&
    allLt 300 (fun k => !(commA 276 cC0.pts[k]! ds[0]! && commA 276 cC0.pts[k]! ds[1]!) ||
      (List.range 5).any fun e => eqA 276 cC0.pts[k]! (powArr 276 co3FiveX0Arr e)) &&
    validA 276 co3FiveTArr

end CFSG.RankThree.Native
