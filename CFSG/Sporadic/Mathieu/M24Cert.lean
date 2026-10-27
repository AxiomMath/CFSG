module

public import Certificates.Data.CFSGNative.Mathieu.M24
public meta import Certificates.Data.CFSGNative.Mathieu.M24
public import Certificates.Certificate3017

public section

namespace CFSG.Sporadic.Mathieu

open CFSG.Sporadic.Mathieu.Native

theorem m24_check : check 24 m24Data = true :=
  Certificates.certificate3017

end CFSG.Sporadic.Mathieu
