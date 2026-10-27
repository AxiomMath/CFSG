module

public import CFSG.Sporadic.J4.QT2LocX0Native

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

@[expose] def nWordU : List Int := [3, 2, 1, 3, 1, 3]

@[expose] def nMask : Nat := 389

@[expose] def nWordV : List Int := [
  -2, -2, -1, -1, -2, -2, 2, 2, 1, 1, 2, 2, -3, -2, -2, -1, -3, -3, 3, 3, 1, 2, 2, 3, -2, -2,
  -3, -3, -2, 2, 3, 3, 2, 2, -1, -3, -1, -1, -3, -2, -3, 2, 1, 3, 1, 3, 2, 2, 1, -3, -1, -3,
  -1, -2, -3]

@[expose] def nRows : Array V2 := mulRows (mulRows (wR nWordU) (etaE nMask)) (wR nWordV)

@[expose] def chkNConj : Bool :=
  eqRows (mulRows nRows (x0GenRows[0]!))
    (mulRows (mulRows (x0GenRows[0]!) (x0GenRows[0]!)) nRows)

end CFSG.Sporadic.J4.QT2
