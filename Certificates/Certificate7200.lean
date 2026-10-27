module

public import Certificates.Data.HeInvPerfect
import Certificates.Kernel.Sporadic.OddCore.He7200F

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four.Native CFSG.Quasithin.E6.HeInvPerfect in
theorem certificate7200 : enumOK 42 heX1CommGens heX1CommEnum = true ∧ heX1CommEnum.tabs.size = 10752 := KernelSpor.He7200.facts7200

end Certificates
