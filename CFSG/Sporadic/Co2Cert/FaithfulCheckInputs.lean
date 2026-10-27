module

public import CFSG.Sporadic.Co2Cert.Check
public import Certificates.Data.CFSGNative.Co2.Data
public import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public import Certificates.Data.CFSGNative.HS.SmallF2
public meta import CFSG.Sporadic.Co2Cert.Check
public meta import Certificates.Data.CFSGNative.Co2.Data
public meta import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public meta import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.Sporadic.Co2Cert

open CFSG.Sporadic.SmallF2.Native

@[expose] def co2RowsA : Array ℕ := rowsOfPayload 22 CFSG.Sporadic.Co2.Native.seedA

@[expose] def co2RowsB : Array ℕ := rowsOfPayload 22 CFSG.Sporadic.Co2.Native.seedB

@[expose] def co2BasisRows : Array ℕ := (co2BasisList.map fun i => co2PackedVecs[i]!).toArray

@[expose] def co2BasisInv : Array ℕ := CFSG.Monster.B.Max2.Native.inv22 co2BasisRows

@[expose] def co2PosTable : Array UInt32 := posTable 22 co2PackedVecs

end CFSG.Sporadic.Co2Cert
