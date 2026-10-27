
module

public import CFSG.Monster.B.TwoA.Fischer.CertGramBase
public meta import CFSG.Monster.B.TwoA.Fischer.CertGramBase
public meta import Certificates.Data.CFSGNative.MonsterB.BinaryRank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer.Cert

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Binary CFSG.Monster.B.Binary.Native
open scoped Matrix

@[expose] def fCol (k i : ℕ) : ℕ := (fColArr[k]!)[i]!

@[expose] def subOneRows (ks : List ℕ) : List ℕ :=
  ks.flatMap fun k =>
    (List.range 78).map fun i => (transposeRows 78 (fColArr[k]!))[i]! ^^^ (1 <<< i)

@[expose] def maskSum : ℕ := [0, 2, 4, 6, 8, 10, 12].foldr (fun p acc => labelCoord p ^^^ acc) 0

@[expose] def fShapeCheck : Bool := fColArr.size == 12 && fColArr.all (·.size == 78)

@[expose] def fColCheck : Bool :=
  (List.range 12).all fun k => (List.range 78).all fun i =>
    fCol k i == labelCoord ((indCandidate k)[basisPt i]!)

@[expose] def fFixCheck : Bool := (List.range 12).all fun k => vecMulN 78 (fColArr[k]!) 949 == 949

@[expose] def coordNeCheck : Bool :=
  (List.range 3510).all fun q => labelCoord q != 949 && decide (labelCoord q < 2 ^ 78)

end CFSG.Monster.B.TwoA.Fischer.Cert
