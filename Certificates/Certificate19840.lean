module

public import Certificates.Data.OverD2Perm
public import Certificates.Data.HSOverData
import Certificates.Kernel.MaxD2.HSP.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate19840 : Certificates.OverD2Perm.checkOver Certificates.HSOver.hsOverDataP
    Certificates.HSOver.hsOverPairW = true := KernelMaxD2.HSP.hsOverP_over

end Certificates
