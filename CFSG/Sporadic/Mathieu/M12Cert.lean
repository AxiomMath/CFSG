module

public import Certificates.Data.CFSGNative.Mathieu.M12
public meta import Certificates.Data.CFSGNative.Mathieu.M12
public import Certificates.Certificate3086

public section

namespace CFSG.Sporadic.Mathieu

open CFSG.Sporadic.Mathieu.Native

theorem m12_check : check 12 m12Data = true :=
  Certificates.certificate3086

end CFSG.Sporadic.Mathieu
