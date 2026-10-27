module

public import Certificates.Data.MaxD2NonComm
public import Certificates.Data.McLFiveLocalP
import Certificates.Kernel.MaxD2.McLP.NonCommGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate9751 : Certificates.MaxD2Heis.checkHNonComm Certificates.MaxD2Heis.mclFiveDataP = true := KernelMaxD2.McLP.mcl_nonComm

end Certificates
