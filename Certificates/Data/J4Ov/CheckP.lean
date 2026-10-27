module

public import Certificates.Data.J4Ov.CheckOrb
public import Certificates.Data.J4Ov.WordsP
public import CFSG.Sporadic.J4.QT2LocCntNative

public section

namespace CFSG.Quasithin.J4Ov

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] def kT : Array (Array V2) := kRowsTab ()

@[expose] def kTi : Array (Array V2) := kT.map invRows

@[expose] def pConj (Zi Z : Array V2) : Array (Array V2) :=
  uBasis.map fun U => conjBy Zi U Z

end CFSG.Quasithin.J4Ov
