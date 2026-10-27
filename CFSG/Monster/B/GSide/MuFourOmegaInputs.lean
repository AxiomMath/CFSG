module

public import CFSG.Monster.Code.Bits
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix

public section

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2

@[expose] def gramArr : Array ℕ :=
  #[13230272, 13505280, 15801344, 8986560, 4792256, 13180864, 49209, 41017, 262202, 131130,
    2097212, 1048636, 62, 129, 65, 193, 61, 514, 258, 59, 2052, 1028, 55, 47]

@[expose] def bWcode (a b : ℕ) : ℕ :=
  popc 24 (Native.actD 22 Native.quotientBasis a &&&
    Native.actD 24 gramArr (Native.actD 22 Native.quotientBasis b)) % 2

end CFSG.Monster.B.GSide
