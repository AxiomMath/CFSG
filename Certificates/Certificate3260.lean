module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDWedgeCert
import Certificates.Kernel.UnitarySix.WedgeW

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix.YamadaD in
theorem certificate3260 : (wedgeCheckNW = true)
    ∧ (wedgeCheckWW = true) :=
  ⟨KernelU6.wedgeCheckNW_true, KernelU6.wedgeCheckWW_true⟩

end Certificates
