module

public import Certificates.Data.CFSGNative.Ru.Data
import Certificates.Kernel.VecCert.RuFinal

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Ru in
theorem certificate3172 : vecCert Native.ruData 3 = true := KernelVec.Ru.vecCert_ru

end Certificates
