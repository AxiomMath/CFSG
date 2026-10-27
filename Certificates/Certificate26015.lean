module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43RankInputs
import Certificates.Kernel.Sporadic.OddCore.CU43SylF

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M24Std.CU43 in
theorem certificate26015 : rankCheck = true := KernelSpor.CU43Syl.facts26015

end Certificates
