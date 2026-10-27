module

public import CFSG.Sporadic.Schreier.Co3SylowCheck
public import Certificates.Data.CFSGNative.Schreier.SetOrbit
public meta import CFSG.Sporadic.Schreier.Co3SylowCheck
public meta import Certificates.Data.CFSGNative.Schreier.SetOrbit

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native

@[expose] def co3MBaseArr : Array Nat :=
  ((co3FinList 276 (by decide) co3MBase).map Fin.val).toArray

@[expose] def co3M1BaseArr : Array Nat :=
  ((co3FinList 276 (by decide) co3M1Base).map Fin.val).toArray

@[expose] def co3MLevels : Array Level := rawLevels 276 co3MArrs co3MBaseArr

end CFSG.Sporadic.Schreier.Co3
