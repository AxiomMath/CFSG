module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Certificate3025
public import CFSG.Certificates.NativeSchreierCard

public section

namespace CFSG.Monster.B.Co2

theorem co2ChainCertOK_eq_true : Native.co2ChainCertOK = true :=
  Certificates.certificate3025

end CFSG.Monster.B.Co2
