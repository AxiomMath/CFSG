module

public import CFSG.Sporadic.SuzRecog.SuzL34Cert.CheckClosure
import Certificates.Kernel.Sporadic.OddCore.SuzClF

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate727304 : CFSG.Sporadic.SuzRecog.SuzL34Cert.l1TabsClosureCheck () = true ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.m21KClosureCheck () = true :=
  ⟨KernelSpor.SuzClF.l1TabsClosureCheck_true, KernelSpor.SuzClF.m21KClosureCheck_true⟩

end Certificates
