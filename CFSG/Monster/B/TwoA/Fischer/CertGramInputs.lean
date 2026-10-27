module

public import CFSG.Monster.B.TwoA.Fischer.CertData
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public meta import CFSG.Monster.B.TwoA.Fischer.CertData
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import CFSG.Monster.B.TwoA.Fischer.CertBin
public import CFSG.Monster.B.TwoA.Fischer.CertBin

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer.Cert

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native
open scoped Matrix

@[expose] def gramWordCheck : Bool :=
  (List.range 78).all fun i =>
    let w := labelWord i
    let h := jWordArr w
    w.all (· < 13) && h[22]! == basisPt i && isInvA 3510 h (invCand 3510 h) &&
      supportBits (jLabelArr w) == ncRow i &&
      gramRow i == ofBits 78 (fun k => (ncRow i).testBit (basisPt k))

@[expose] def gramInvCheck : Bool := mulRows 78 gramRowArr (invMat 78 gramRowArr) == idRows 78

@[expose] def coordCheck : Bool :=
  ((List.range 78).all fun i => labelCoord (basisPt i) == 2 ^ i) &&
    let gT := transposeRows 78 gramRowArr
    (List.range 3510).all fun y =>
      vecMulN 78 gT (labelCoord y) == ofBits 78 (fun i => (ncRow i).testBit y)

end CFSG.Monster.B.TwoA.Fischer.Cert
