module

public import Certificates.Data.SmithL6Faith
import Certificates.Kernel.SmithL6K.GlueT

public section

namespace Certificates

open CertificateChecks

theorem certificate38608 : CFSG.SmithL6.chkTvArrInj = true := KernelSmithL6K.tvArrInj_holds

end Certificates
