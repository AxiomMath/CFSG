module

public import Certificates.Data.CFSGNative.SectionRank.Elem3
public import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.SectionRank.Native

open CFSG.Sporadic.SmallF2.Native

@[expose] def ops2 (d : Nat) : Ops (Array Nat) Nat where
  decode := rowsOfPayload d
  mul := mulRows d
  one := idRows d
  eq X Y := X == Y
  vmul v X := vecMulN d X v
  unit k := 1 <<< k
  vne u w := (List.range d).any fun j => u.testBit j != w.testBit j

end CFSG.SectionRank.Native
