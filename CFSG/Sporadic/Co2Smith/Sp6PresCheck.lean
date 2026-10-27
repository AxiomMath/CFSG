module

public import CFSG.Sporadic.Co2Smith.Check
public import Certificates.Data.CFSGNative.Co2Smith.Sp6Pres
public import Certificates.Certificate10085
public meta import CFSG.Sporadic.Co2Smith.Check
public meta import Certificates.Data.CFSGNative.Co2Smith.Sp6Pres

set_option compiler.extract_closed false

public section

namespace CFSG.Sporadic.Co2Smith

theorem sp6Check_ok : Native.sp6Check seedRowsArr = true :=
  Certificates.certificate10085

end CFSG.Sporadic.Co2Smith
