module

public import Certificates.Data.CFSGNative.He.Fp
public import Certificates.Data.CFSGNative.HN.Data
public meta import Certificates.Data.CFSGNative.He.Fp
public meta import Certificates.Data.CFSGNative.HN.Data
public import CFSG.Sporadic.HNSchreier.SeedsCheckInputs
public import Certificates.Certificate2106

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.Sporadic.He.Native

theorem seed_orders_cert : seedChecks rowsA rowsB = true :=
  Certificates.certificate2106

end CFSG.Sporadic.HNSchreier.Native
