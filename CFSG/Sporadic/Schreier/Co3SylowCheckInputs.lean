module

public import CFSG.Sporadic.Schreier.Co3Outer
public import CFSG.Sporadic.Schreier.Co3OrderCheck
public meta import CFSG.Sporadic.Schreier.Co3Outer
public meta import CFSG.Sporadic.Schreier.Co3OrderCheck

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native

@[expose] def co3TBaseArr : Array Nat :=
  ((co3FinList 276 (by decide) co3TBase).map Fin.val).toArray

@[expose] def co3ChainLevels : Array Level := rawLevels 276 co3ChainArrs co3ChainBaseArr

@[expose] def co3TLevels : Array Level := rawLevels 276 co3TArrs co3TBaseArr

end CFSG.Sporadic.Schreier.Co3
