module

public import Certificates.Data.CFSGNative.Fi22.Certificate
public meta import Certificates.Data.CFSGNative.Fi22.Certificate
public import Certificates.Certificate1005

public section

namespace CFSG.Sporadic.Fi22

open Native

theorem fi22_certificate : fi22Certificate 3 = true :=
  Certificates.certificate1005

end CFSG.Sporadic.Fi22
