
module

public import CFSG.Sporadic.Suz.CertificateBase

public import Certificates.Data.CFSGNative.Suz.Certificate
public meta import Certificates.Data.CFSGNative.Suz.Certificate
public import Certificates.Certificate3173
public import Certificates.Certificate3173Base

public section

namespace CFSG.Sporadic.Suz

open Native

theorem suz_certificate : suzCertificate 3 = true :=
  Certificates.certificate3173

end CFSG.Sporadic.Suz
