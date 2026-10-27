module

public import Certificates.Data.CFSGNative.Mathieu.M11
public meta import Certificates.Data.CFSGNative.Mathieu.M11
public import Certificates.Certificate3120

public section

namespace CFSG.Sporadic.Mathieu

open CFSG.Sporadic.Mathieu.Native

theorem m11_check : check 11 m11Data = true :=
  Certificates.certificate3120

end CFSG.Sporadic.Mathieu
