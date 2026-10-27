module

public import Certificates.Data.McLCentOver
import Certificates.Kernel.MaxD2.McLP.CentGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate19900 : Certificates.MclCentOver.checkCentOver Certificates.MaxD2Heis.mclFiveDataP = true := KernelMaxD2.McLP.mcl_centOver

end Certificates
