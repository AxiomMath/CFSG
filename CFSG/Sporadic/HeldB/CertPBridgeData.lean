module

public import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Sporadic.HeldB

open CFSG.Monster.B.Co2.Native

@[expose] def heBridgeHex : String := include_str "Data"/"Bridge.txt"

@[expose] def heBridgeArr : Array Nat := hexTable 4 8330 0 heBridgeHex

end CFSG.Sporadic.HeldB
