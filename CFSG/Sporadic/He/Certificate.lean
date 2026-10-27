module

public import Certificates.Data.CFSGNative.He.Certificate
public meta import Certificates.Data.CFSGNative.He.Certificate
public import Certificates.Certificate3168

public section

namespace CFSG.Sporadic.He

open Native

theorem he_certificate : heCertificate 3 = true :=
  Certificates.certificate3168

end CFSG.Sporadic.He
