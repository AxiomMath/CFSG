module

public import Certificates.Certificate21126
public import Certificates.Certificate21127

public section

namespace CFSG.Sporadic.Co2Smith

theorem glRoot_check : Native.glRootOK = true :=
  Certificates.certificate21126

theorem glChainG0_check : Native.glChainG0OK = true :=
  Certificates.certificate21127

end CFSG.Sporadic.Co2Smith
