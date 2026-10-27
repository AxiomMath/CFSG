module

public import Certificates.Data.CFSGNative.J1.Certificate
public meta import Certificates.Data.CFSGNative.J1.Certificate
public import Certificates.Certificate3119

public section

namespace CFSG.Sporadic.J1

open Native

theorem j1_certificate : j1Certificate 3 = true :=
  Certificates.certificate3119

end CFSG.Sporadic.J1
