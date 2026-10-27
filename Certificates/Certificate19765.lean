module

public import Certificates.Data.McLFiveLocalR
import Certificates.Kernel.MaxD2.McLR.HeisGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate19765 : Certificates.MaxD2Heis.checkHeis Certificates.MaxD2Heis.mclFiveDataR = true := KernelMaxD2.McLR.mcl_heis

end Certificates
