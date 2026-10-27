module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.SuzCheck
import Certificates.Kernel.Sporadic.OddCore.S129062F

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic in
theorem certificate129062 : suzRankCheck () = true := KernelSpor.S129062.rank_true

end Certificates
