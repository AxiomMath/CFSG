module

public import Certificates.Data.McLFiveLocalR
public import Certificates.Data.MaxD2TI
import Certificates.Kernel.MaxD2.McLR.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate41721 : Certificates.MaxD2TI.checkTI Certificates.MaxD2Heis.mclFiveDataR = true := KernelMaxD2.McLR.mcl_ti

end Certificates
