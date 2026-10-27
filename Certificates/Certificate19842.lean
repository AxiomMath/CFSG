module

public import Certificates.Data.OverD2Perm
public import Certificates.Data.HSOverData
import Certificates.Kernel.MaxD2.HSP.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate19842 : Certificates.OverD2Perm.checkClosedPair Certificates.HSOver.hsOverDataP 16 = true := KernelMaxD2.HSP.hsOverP_closed

end Certificates
