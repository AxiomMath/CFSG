
module

public import CFSG.Monster.B.Short.OrbitCertBase

public import Certificates.Data.CFSGNative.MonsterB.Short
public meta import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Certificate3014
public import Certificates.Certificate3014Base

public section

namespace CFSG.Monster.B.Short

theorem shortCertOK_eq_true : Native.shortCertOK = true :=
  Certificates.certificate3014

end CFSG.Monster.B.Short
