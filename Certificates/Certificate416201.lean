module

public import Certificates.Data.U43SProp
import Certificates.Kernel.PermCent.U43SpGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate416201 : CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M.spCountCheck () = true :=
  KernelPermCent.U43Sp.spCountCheck_true

end Certificates
