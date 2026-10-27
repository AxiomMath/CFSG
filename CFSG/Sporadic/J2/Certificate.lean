module

public import Certificates.Data.CFSGNative.J2.Certificate
public meta import Certificates.Data.CFSGNative.J2.Certificate
public import Certificates.Certificate3139

public section

namespace CFSG.Sporadic.J2

open Native

theorem j2_certificate : j2Certificate 3 = true :=
  Certificates.certificate3139

end CFSG.Sporadic.J2
