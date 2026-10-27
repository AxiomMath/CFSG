
module

public import CFSG.Quasithin.Vol2.KGFactC31RuCand
import Certificates.Kernel.Misc.RuScan.Cand

public section

open CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31.Ru

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31.Ru in
theorem certificate7230 : ∀ c ∈ ruC, cosetH 0 * c * ruZ * (cosetH 0 * c)⁻¹ ≠ ruZ →
    ∀ es q, (es, q) ∈ ruGroups → CandConcl 0 (cosetH 0 * c) ruZ es q :=
  fun _ hc hmv _ _ hes => KernelMisc.RuScan.candFactC (by norm_num) hc hmv hes

end Certificates

end
