
module

public import CFSG.Monster.B.Fischer.Fi22LocalCheckBase
public import Certificates.Data.CFSGNative.Schreier.Enum3
public import Mathlib.Data.Fintype.Prod
public meta import CFSG.Monster.B.Fischer.Fi22LocalCheckBase
public meta import Certificates.Data.CFSGNative.Schreier.Enum3
public meta import Mathlib.Data.Fintype.Prod

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def fi22TLevels : Array Level :=
  rawLevels 3510 (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4]

@[expose] def fi22TPointsArr : Array ℕ := fi22OuterTPointsNat.toArray

@[expose] def fi22CoverWit : Array (ℕ × ℕ × ℕ × ℕ) :=
  conjSearch3 3510 fi22TLevels #[0, 1, 2, 3, 6, 4] ((fi22OuterStrong3510 4).extract 0 9)
    (fi22OuterStrong3510 7)

end CFSG.Monster.B.Fischer
