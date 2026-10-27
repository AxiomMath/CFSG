module

public import Certificates.Data.HuppertU38Fix.Check
import Certificates.Kernel.U38Fix.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate419001 : U38Fix.u38FixAllCheck () = true := KernelU38Fix.all_true

end Certificates
