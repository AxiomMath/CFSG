
module

public import CFSG.Sporadic.ON.CertificateBase

public import Certificates.Data.CFSGNative.ON.Certificate
public meta import Certificates.Data.CFSGNative.ON.Certificate
public import Certificates.Certificate3171
public import Certificates.Certificate3171Base

public section

namespace CFSG.Sporadic.ON

open Native

theorem on_certificate : onCertificate 3 = true :=
  Certificates.certificate3171

end CFSG.Sporadic.ON
