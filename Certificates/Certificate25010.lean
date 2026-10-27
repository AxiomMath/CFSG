module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.FoursCheck
import Certificates.Kernel.EvenSporSuz.Fours25010F

public section

namespace CertificateChecks.Batch25010

theorem foursWitnessCheck_0 : CFSG.EvenSporadicStandard.TwoSuz.foursWitnessCheck = true :=
  KernelSpor.S26990.check25010

end CertificateChecks.Batch25010

namespace Certificates

open CertificateChecks

theorem certificate25010 : CFSG.EvenSporadicStandard.TwoSuz.foursWitnessCheck = true := CertificateChecks.Batch25010.foursWitnessCheck_0

end Certificates
