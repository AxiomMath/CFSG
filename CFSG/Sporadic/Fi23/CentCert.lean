module

public import Certificates.Data.CFSGNative.Fi23.Centralizer
public meta import Certificates.Data.CFSGNative.Fi23.Centralizer
public import Certificates.Certificate1011

public section

namespace CFSG.Sporadic.Fi23

open Native

theorem cent_certificate : centCertificate 3 = true :=
  Certificates.certificate1011

end CFSG.Sporadic.Fi23
