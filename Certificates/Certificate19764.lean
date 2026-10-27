module

public import Certificates.Data.McLFiveLocalP
import Certificates.Kernel.MaxD2.McLP.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate19764 : Certificates.MaxD2Heis.checkHeis Certificates.MaxD2Heis.mclFiveDataP = true := KernelMaxD2.McLP.mcl_heis

end Certificates
