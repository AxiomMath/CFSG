module

public import Certificates.Certificate21160
public import Certificates.Certificate21162

public section

namespace CFSG.Sporadic.Co2Smith

theorem glMark_check : Native.glMarkOK = true :=
  Certificates.certificate21160

theorem glMkFix_check : Native.glMkFixOK = true :=
  Certificates.certificate21162

end CFSG.Sporadic.Co2Smith
