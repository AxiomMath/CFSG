module

public import Certificates.Data.HuppertReeEight.Checker
import Certificates.Kernel.TitsW.P188009

public section

namespace Certificates

open CertificateChecks

theorem certificate188009 : HuppertReeEight.sylowCheck () = true ∧ HuppertReeEight.coverCheck () = true ∧
    HuppertReeEight.genCheck () = true :=
  ⟨KernelTitsW.P188009.sylow, KernelTitsW.P188009.cover, KernelTitsW.P188009.gen⟩

end Certificates
