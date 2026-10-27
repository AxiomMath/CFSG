module

public import CFSG.Sporadic.SuzRecog.SuzL34.Facts
import Certificates.Kernel.Sporadic.OddCore.SuzBtXG
import Certificates.Kernel.Sporadic.OddCore.SuzBtYG

public section

namespace Certificates

open CertificateChecks.KernelSpor

open CFSG in
theorem certificate727302 : CFSG.Sporadic.SuzRecog.SuzL34Cert.F9Prop ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.F11Prop :=
  ⟨SuzBtYG.f9Prop, SuzBtXG.f11Prop⟩

end Certificates
