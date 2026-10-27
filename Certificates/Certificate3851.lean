module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitSylowData
import Certificates.Kernel.OmegaEight.Dict3851Checks

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.NSplit CFSG.EvenSmallLie.OmegaEight.Stage1 in
theorem certificate3851 : (dictCheck .plus = true)
    ∧ (dictCheck .minus = true) := KernelO8.Dict.cert3851

end Certificates
