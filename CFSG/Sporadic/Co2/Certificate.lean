module

public import Certificates.Data.CFSGNative.Co2.Data
public meta import Certificates.Data.CFSGNative.Co2.Data
public import Certificates.Certificate3138

public section

namespace CFSG.Sporadic.Co2

open CFSG.Sporadic.SmallF2.Native

theorem co2_certificate : vecCert Native.co2Data 3 = true :=
  Certificates.certificate3138

end CFSG.Sporadic.Co2
