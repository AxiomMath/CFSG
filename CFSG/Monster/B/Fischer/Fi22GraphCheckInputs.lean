module

public import CFSG.Monster.B.Fischer.Fi22GraphData
public import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Monster.B.Fischer.Fi22GraphData
public meta import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2.Native

@[expose] def fi22GraphOuterArr : Array Nat :=
  Array.ofFn (n := 3510) fun i =>
    CFSG.Monster.B.Max2.Native.hexAt fi22GraphOuterHex.toUTF8 (3 * i.val) 3

end CFSG.Monster.B.Fischer
