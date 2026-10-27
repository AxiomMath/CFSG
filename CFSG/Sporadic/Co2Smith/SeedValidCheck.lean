module

public import CFSG.Sporadic.Co2Smith.Check
public import Certificates.Data.CFSGNative.Co2Smith.SeedValid
public import Certificates.Certificate10083
public meta import CFSG.Sporadic.Co2Smith.Check
public meta import Certificates.Data.CFSGNative.Co2Smith.SeedValid

set_option compiler.extract_closed false

public section

namespace CFSG.Sporadic.Co2Smith

theorem seedsValid_check : Native.seedsValidOK seedRowsArr = true :=
  Certificates.certificate10083

end CFSG.Sporadic.Co2Smith
