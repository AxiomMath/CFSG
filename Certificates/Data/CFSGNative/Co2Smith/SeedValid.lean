module

public import Certificates.Data.CFSGNative.Co2Smith.Check

public section

namespace CFSG.Sporadic.Co2Smith.Native

@[expose] def seedsValidOK (seeds : Array (Array Nat)) : Bool :=
  validM seeds[0]! && validM seeds[1]!

end CFSG.Sporadic.Co2Smith.Native
