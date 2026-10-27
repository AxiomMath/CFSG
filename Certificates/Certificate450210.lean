module

public import Certificates.Data.RouteP.M24Defect
import Certificates.Kernel.RouteP.M24Def.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate450210 : Certificates.RouteP.M24Defect.checkAll () = true :=
  KernelM24Def.checkAll_true

end Certificates
