module

public import Certificates.Data.Kernel.F2AlgRank
public import Certificates.Kernel.Co1N4Spin.Data
public import Certificates.Kernel.Co1M.Regs10071
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo1N4Spin

open CFSG.KC.F2AlgRank CFSG.KC.Co1F2 CertificateChecks.KernelCo1M

@[expose] noncomputable def gens : List Nat := [getL 0 cmRP71 23, getL 0 cmRP71 17]

theorem sep_ok : sepK 24 gens tree masks S F Dm t 10075731 = true := by quickRfl

end CertificateChecks.KernelCo1N4Spin

end
