module

public import Certificates.Data.CFSGNative.Fi23.Tr
public meta import Certificates.Data.CFSGNative.Fi23.Tr
public import Certificates.Certificate1015

public section

namespace CFSG.Sporadic.Fi23

open Native

theorem tr_certificate : trCertificate 3 = true :=
  Certificates.certificate1015

end CFSG.Sporadic.Fi23
