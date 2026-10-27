module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzPinCheck
import Certificates.Kernel.Sporadic.OddCore.Suz26990F

public section

namespace Certificates

open CertificateChecks

theorem certificate26990 : CFSG.EvenSporadicStandard.Induction.suzPinCheck = true := KernelSpor.S26990.check26990

end Certificates
