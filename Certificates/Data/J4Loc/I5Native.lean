module

public import Certificates.Data.J4Loc.Native
public import CFSG.Sporadic.J4.QT2LocNative

public section

namespace CFSG.Quasithin.J4Loc

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] def i5Pairs : List (Nat × Nat) :=
  [(965, 1243), (1979, 1979), (1243, 965), (165, 165), (864, 1150), (1822, 1822), (1150, 864)]

@[expose] def i5Masks : List Nat := srt (0 :: i5Pairs.map Prod.fst)

end CFSG.Quasithin.J4Loc
