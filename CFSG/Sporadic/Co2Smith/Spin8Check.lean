module

public import Certificates.Data.CFSGNative.Co2Smith.Spin8
public import Certificates.Certificate10086
public meta import Certificates.Data.CFSGNative.Co2Smith.Spin8

public section

namespace CFSG.Sporadic.Co2Smith

theorem spinCheck_ok : Native.spinCheck = true :=
  Certificates.certificate10086

end CFSG.Sporadic.Co2Smith
