module

public import Certificates.Data.SmithL6Coll
import Certificates.Kernel.SmithL6Coll.Assemble

public section

namespace Certificates

open CertificateChecks

theorem certificate38607 : CFSG.SmithL6.chkColl = true := KernelSmithL6Coll.chkColl_holds

end Certificates
