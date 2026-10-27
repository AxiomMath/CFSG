module

public import Certificates.Data.CFSGNative.HS.Data
public meta import Certificates.Data.CFSGNative.HS.Data
public import Certificates.Certificate3167

public section

namespace CFSG.Sporadic.HS

open CFSG.Sporadic.SmallF2.Native

theorem hs_certificate : vecCert Native.hsData 3 = true :=
  Certificates.certificate3167

end CFSG.Sporadic.HS
