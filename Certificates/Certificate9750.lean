module

public import Certificates.Data.MaxD2NonComm
public import Certificates.Data.TitsFiveLocal
import Certificates.Kernel.MaxD2.TitsD.TransGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate9750 : Certificates.MaxD2Perm.checkNonComm Certificates.MaxD2Perm.titsDData = true := KernelMaxD2.TitsD.titsD_nonComm

end Certificates
