module

public import Certificates.Data.OverD2Perm
public import Certificates.Data.HSOverData
import Certificates.Kernel.MaxD2.HSOver.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate19841 : Certificates.OverD2Perm.checkMaximal Certificates.HSOver.hsOverDataR = true := KernelMaxD2.HSOver.hsOver_maximal

end Certificates
