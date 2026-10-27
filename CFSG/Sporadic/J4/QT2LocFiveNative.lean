module

public import CFSG.Sporadic.J4.QTMask
public import Certificates.Data.CFSGNative.J4.Cert

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] def fiveWord : List Int := [1, 2, -3, 1, 2, -3]

@[expose] def fiveRows : Array V2 := wordRows (locMats ()) (locInvs ()) fiveWord

@[expose] def chkFivePow : Bool := eqRows (powRows fiveRows 5) idRows

@[expose] def fiveAct (c : Nat) : Nat := fiveWord.foldr act c

@[expose] def fiveFixed : List Nat := (List.range 2048).filter fun c => fiveAct c == c

@[expose] def chkFiveMasks : Bool :=
  (List.range 2048).all (fun c => decide (fiveAct c < 2048)) && fiveFixed.length == 8 &&
    fiveAct 1 != 1

end CFSG.Sporadic.J4.QT2
