module

public import CFSG.LocalAnalysis.OddStandard.Solomon75T11bGen4Lift
import Certificates.Kernel.S75Gen4.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.Solomon75.AhatData in
theorem certificate6132 : Gen4Good 10 (P0 10) ∧ Gen4Good 11 (P0 11) :=
  ⟨KernelS75Gen4.gen4Good10, KernelS75Gen4.gen4Good11⟩

end Certificates
