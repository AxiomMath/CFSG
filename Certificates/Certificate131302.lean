module

public import CFSG.HardMathSupport.Foote.E27.SporMData
import Certificates.Kernel.E27Spor.MOrbFacts

public section

namespace Certificates

open CFSG.HardMathSupport.Foote.E27 in
theorem certificate131302 : 3 ^ 7 ∣ Nat.card MAct.K :=
  CertificateChecks.KernelE27Spor.MOrb.three_pow_dvd

end Certificates
