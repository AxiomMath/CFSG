module

public import Certificates.Data.CFSGNative.Mathieu.M22
public meta import Certificates.Data.CFSGNative.Mathieu.M22
public import Certificates.Certificate3029

public section

namespace CFSG.Sporadic.Mathieu

open CFSG.Sporadic.Mathieu.Native

theorem m22_check : check 22 m22Data = true :=
  Certificates.certificate3029

end CFSG.Sporadic.Mathieu
