module

public import Certificates.Data.MaxD2PermTrans
public import Certificates.Data.TitsFiveLocal
import Certificates.Kernel.MaxD2.TitsD.TransGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate9516 : Certificates.MaxD2Perm.checkTrans Certificates.MaxD2Perm.titsDData = true := KernelMaxD2.TitsD.titsD_trans

end Certificates
