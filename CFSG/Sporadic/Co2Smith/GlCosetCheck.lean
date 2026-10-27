module

public import Certificates.Certificate21170
public import Certificates.Certificate21171
public import Certificates.Certificate21172
public import Certificates.Certificate21173

public section

namespace CFSG.Sporadic.Co2Smith

theorem glCosetElem_check : Native.glCosetElemOK = true :=
  Certificates.certificate21170

theorem glChainM2_check : Native.glChainM2OK = true :=
  Certificates.certificate21171

theorem glChainCz_check : Native.glChainCzOK = true :=
  Certificates.certificate21172

theorem glCosetLab_check : Native.glCosetLabOK = true :=
  Certificates.certificate21173

end CFSG.Sporadic.Co2Smith
