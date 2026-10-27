module

public import CFSG.Sporadic.J4.QTNative

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] def mixMats : Array (Array V2) := baseMats ++ locMats ()

@[expose] def mixInvs : Array (Array V2) := baseInvs ++ locInvs ()

@[expose] def mixRowsOf (w : List Int) : Array V2 := wordRows mixMats mixInvs w

@[expose] def gWord : List Int := [-4, -3, -4, 3, -4, -2, -2, -2, -1, -2, 4, -3, 4, 3, 4]

@[expose] def y7Word : List Int :=
  [-4, -3, -4, 3, -4, 2, 1, 2, 2, 2, 4, -3, 4, 3, 4, 5, 3, 5, 5, -4, -3]

@[expose] def y11Word : List Int :=
  [-4, -3, -4, 3, -4, 2, 1, 2, 2, 2, 4, -3, 4, 3, 4, -4, 5, 5, 3, 5, 3, 5, 3, 3, -4]

@[expose] def chkCommRoot (loc inv : Array (Array V2)) (w : List Int) : Bool :=
  let T := uTab loc inv
  let z := etaRows T 11 1131
  let G := mixRowsOf w
  eqRows (mulRows G z) (mulRows z G) && differs (frApply (frTable G) rootV) rootV

@[expose] def chkOrder (loc inv : Array (Array V2)) (w : List Int) (p : Nat) : Bool :=
  chkCommRoot loc inv w && eqRows (powRows (mixRowsOf w) p) idRows

end CFSG.Sporadic.J4.QT2
