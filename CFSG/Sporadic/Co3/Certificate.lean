module

public import Certificates.Data.CFSGNative.Co3.Data
public meta import Certificates.Data.CFSGNative.Co3.Data
public import Certificates.Certificate3091

public section

namespace CFSG.Sporadic.Co3

open CFSG.Sporadic.SmallF2.Native

theorem co3_certificate : vecCert Native.co3Data 3 = true :=
  Certificates.certificate3091

end CFSG.Sporadic.Co3
