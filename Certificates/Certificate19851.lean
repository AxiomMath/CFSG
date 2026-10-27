module

public import Certificates.Data.HSFiveU35Data
import Certificates.Kernel.MaxD2.HSU.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate19851 : Certificates.MaxD2Heis.checkHeis Certificates.HSU35.dataU = true := KernelMaxD2.HSU.hsU_heis

end Certificates
