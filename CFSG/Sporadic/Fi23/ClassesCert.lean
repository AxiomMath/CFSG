module

public import Certificates.Data.CFSGNative.Fi23.Classes
public meta import Certificates.Data.CFSGNative.Fi23.Classes
public import Certificates.Certificate1013

public section

namespace CFSG.Sporadic.Fi23

open Native

theorem classes_certificate : classesCertificate 3 = true :=
  Certificates.certificate1013

end CFSG.Sporadic.Fi23
