module

public import CFSG.Sporadic.Co2Smith.Check
public import Certificates.Data.CFSGNative.Co2Smith.Pin
public import Certificates.Certificate10082
public meta import CFSG.Sporadic.Co2Smith.Check
public meta import Certificates.Data.CFSGNative.Co2Smith.Pin

set_option compiler.extract_closed false

public section

namespace CFSG.Sporadic.Co2Smith

theorem frameNe_check : Native.frameNeOK seedRowsArr = true :=
  Certificates.certificate10082.1

theorem pinUnique_check : Native.pinUniqueOK = true :=
  Certificates.certificate10082.2

end CFSG.Sporadic.Co2Smith
