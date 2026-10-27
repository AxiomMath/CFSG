module

public import Certificates.Data.CFSGNative.J3.Data
public meta import Certificates.Data.CFSGNative.J3.Data
public import Certificates.Certificate3169

public section

namespace CFSG.Sporadic.J3

open Native

theorem j3_check : check j3Data 3 = true :=
  Certificates.certificate3169

end CFSG.Sporadic.J3
