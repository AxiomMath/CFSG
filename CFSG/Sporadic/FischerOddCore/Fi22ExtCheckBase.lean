
module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtData
public import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtData
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs

@[expose] public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

@[expose] def fi22ExtSmallStrong : Array (Array Nat) :=
  Array.ofFn (n := 18) fun j => fi22ExtArr256 j.val

end CFSG.Sporadic.FischerOddCore
