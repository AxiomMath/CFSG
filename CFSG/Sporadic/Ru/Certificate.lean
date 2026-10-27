module

public import Certificates.Data.CFSGNative.Ru.Data
public meta import Certificates.Data.CFSGNative.Ru.Data
public import Certificates.Certificate3172

public section

namespace CFSG.Sporadic.Ru

open CFSG.Sporadic.SmallF2.Native

theorem ru_certificate : vecCert Native.ruData 3 = true :=
  Certificates.certificate3172

end CFSG.Sporadic.Ru
