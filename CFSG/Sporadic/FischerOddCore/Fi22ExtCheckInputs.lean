
module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtData
public import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtData
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

@[expose] def fi22ExtBytes3510 : ByteArray := fi22Ext3510Text.toUTF8

@[expose] def fi22ExtBytes256 : ByteArray := fi22Ext256Text.toUTF8

@[expose] def fi22ExtArr (L : Nat) : Array Nat := hexLine fi22ExtBytes3510 3 3510 L

@[expose] def fi22ExtArr256 (L : Nat) : Array Nat := hexLine fi22ExtBytes256 2 256 L

@[expose] def fi22ExtSmallPointsNat : List Nat := hex3List fi22ExtSmallPointsHex 256

end CFSG.Sporadic.FischerOddCore
