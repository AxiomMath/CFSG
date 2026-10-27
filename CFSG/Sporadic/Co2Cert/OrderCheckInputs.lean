module

public import CFSG.Sporadic.Co2Cert.Check
public import CFSG.Monster.B.Mathieu.SylowCore
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.Co2Cert.Check
public meta import CFSG.Monster.B.Mathieu.SylowCore
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.Co2Cert

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu

@[expose] def co2WArr : Array ℕ :=
  compA 2300 (invCand 2300 co2OrigArrs[0]!) (compA 2300 co2OrigArrs[1]! (compA 2300
    co2OrigArrs[1]! (compA 2300 co2OrigArrs[0]! (compA 2300 co2OrigArrs[1]!
      (invCand 2300 co2OrigArrs[0]!)))))

@[expose] def co2cProdArr : Array ℕ := compA 2300 co2cOrigArrs[0]! co2cOrigArrs[1]!

end CFSG.Sporadic.Co2Cert
