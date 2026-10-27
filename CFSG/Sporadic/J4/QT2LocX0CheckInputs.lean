module

public import CFSG.Sporadic.J4.QT2LocX0Native

public section

namespace CFSG.Sporadic.J4.QT2

@[expose] def chkX0All : Bool :=
  chkX0Gens && chkX0Orb && chkX0Conj && chkX0Invs && chkX0Pts

end CFSG.Sporadic.J4.QT2
