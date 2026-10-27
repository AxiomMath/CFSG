module

public import CFSG.Sporadic.J4.QTRankWitNative

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4.Native

@[expose] def xRowsOf (ℓ : Int) : Array V2 := xRows (locMats ()) (locInvs ()) ℓ

@[expose] def wordRowsOf (w : List Int) : Array V2 := wordRows (locMats ()) (locInvs ()) w

@[expose] def triOK (vs : Array V2) (ps : Array Nat) : Bool :=
  vs.size == ps.size && (List.range vs.size).all fun k =>
    (vs[k]!).wf && decide (ps[k]! < 112) && (vs[k]!).testBit ps[k]! &&
      (List.range k).all fun j => !((vs[k]!).testBit ps[j]!)

end CFSG.Sporadic.J4.QT
