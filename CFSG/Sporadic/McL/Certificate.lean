module

public import Certificates.Data.CFSGNative.McL.Certificate
public meta import Certificates.Data.CFSGNative.McL.Certificate
public import Certificates.Certificate3170

public section

namespace CFSG.Sporadic.McL

open Native

theorem mcl_certificate : mclCertificate 3 = true :=
  Certificates.certificate3170

end CFSG.Sporadic.McL
