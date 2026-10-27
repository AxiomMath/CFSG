
module

public import CFSG.Sporadic.Co1.CertificateBase

public import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Data
public import Certificates.Certificate3024

public section

namespace CFSG.Sporadic.Co1

open CFSG.Sporadic.SmallF2.Native

theorem co1_certificate : vecCert Native.co1Data 3 = true :=
  Certificates.certificate3024

end CFSG.Sporadic.Co1
