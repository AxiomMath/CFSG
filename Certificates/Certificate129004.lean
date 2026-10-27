module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co3Check
import Certificates.Kernel.Sporadic.OddCore.Co3HeisF

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic in
theorem certificate129004 : co3HeisCheck () = true := KernelSpor.Co3Fus.facts129004

end Certificates
