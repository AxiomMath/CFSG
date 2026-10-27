
module


public import CFSG.GH74.GLS.C3.Layer2.FinModelFactsMath
import Certificates.Kernel.FinModel5040.C5040

public section

namespace Certificates

open CFSG.GH74.GLS.C3.Layer2.Model.Facts in
theorem certificate5040 : FactsProp 6 ∧ FactsProp 7 :=
  ⟨CertificateChecks.KernelFM5040.facts6, CertificateChecks.KernelFM5040.facts7⟩

end Certificates
