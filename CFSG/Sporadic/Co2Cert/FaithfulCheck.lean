
module

public import CFSG.Sporadic.Co2Cert.FaithfulCheckBase

public import CFSG.Sporadic.Co2Cert.Check
public import Certificates.Data.CFSGNative.Co2.Data
public import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public import Certificates.Data.CFSGNative.HS.SmallF2
public meta import CFSG.Sporadic.Co2Cert.Check
public meta import Certificates.Data.CFSGNative.Co2.Data
public meta import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public import CFSG.Sporadic.Co2Cert.FaithfulCheckInputs
public import Certificates.Certificate3116
public import Certificates.Certificate3116Base

public section

namespace CFSG.Sporadic.Co2Cert

open CFSG.Sporadic.SmallF2.Native

theorem co2Faithful_check :
    co2PackedVecs.size = 2300 ∧
    (∀ i < 2300, co2PackedVecs[i]! < 2 ^ 22 ∧ co2PackedVecs[i]! ≠ 0 ∧
      ∀ j < 2300, co2PackedVecs[i]! = co2PackedVecs[j]! → i = j) ∧
    co2BasisRows.size = 22 ∧ mulRows 22 co2BasisInv co2BasisRows = idRows 22 ∧
    (∀ i < 2300, vecMulN 22 (transposeRows 22 co2RowsA) co2PackedVecs[i]! =
      co2PackedVecs[(co2OrigArrs[0]!)[i]!]!) ∧
    (∀ i < 2300, vecMulN 22 (transposeRows 22 co2RowsB) co2PackedVecs[i]! =
      co2PackedVecs[(co2OrigArrs[1]!)[i]!]!) ∧
    mulRows 22 co2RowsA co2RowsA = idRows 22 ∧ powRows 22 co2RowsB 5 = idRows 22 :=
  Certificates.certificate3116

end CFSG.Sporadic.Co2Cert
