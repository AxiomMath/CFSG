module

public import Certificates.Data.J4Loc.Native

public section

namespace CFSG.Quasithin.J4Rad

open CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc

@[expose] def actW : List Int → Nat → Nat
  | [], c => c
  | ℓ :: w, c => actW w (act ℓ c)

@[expose] def wordA : List Int := [1, 2, -3, -1, 3, 3, -2]

@[expose] def wordB : List Int := [-2, 1, -2, -1, 2, 1, 2, -3]

@[expose] def imgW (w : List Int) (W : List Nat) : List Nat := srt (W.map (actW w))

end CFSG.Quasithin.J4Rad
