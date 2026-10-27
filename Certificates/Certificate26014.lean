module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43RankInputs
import Certificates.Kernel.Sporadic.OddCore.CU43SylEF

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M24Std.CU43 in
theorem certificate26014 : (sylPermCheck = true) ∧ (sylInPCheck = true) ∧ (sylEnumCheck = true) := KernelSpor.CU43SylE.facts26014

end Certificates
