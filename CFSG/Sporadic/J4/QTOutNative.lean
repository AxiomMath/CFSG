module

public import CFSG.Sporadic.J4.QTRankNative
public import CFSG.Sporadic.J4.QTOutData

public section

namespace CFSG.Sporadic.J4.QT

@[expose] def stepIn (L L' : List Nat) : Bool :=
  L'.all fun c => tabL.all fun t => L.contains (c ^^^ actT t c)

@[expose] def stepOut (L L' : List Nat) : Bool :=
  (List.range 2048).all fun c => L'.contains c || tabL.any fun t => !L.contains (c ^^^ actT t c)

@[expose] def stepFaithful (L : List Nat) : Bool :=
  tabL.all fun t => t == idT || (List.range 11).any fun j => !L.contains (actT t (2 ^ j) ^^^ 2 ^ j)

@[expose] def ucsStep (L L' : List Nat) : Bool := stepIn L L' && stepOut L L' && stepFaithful L

@[expose] def tET : List Nat := seqT (pcSeq eT)

@[expose] def fixesZ4 (t : List Nat) : Bool := (ucsMasks.getD 4 []).all fun w => actT t w == w

end CFSG.Sporadic.J4.QT
