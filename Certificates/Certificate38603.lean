module

public import Certificates.Kernel.SmithL6K.GlueU

public section

namespace Certificates

open CertificateChecks

theorem certificate38603 : CFSG.SmithL6.chkUa = true := KernelSmithL6K.chkUa_holds

end Certificates
