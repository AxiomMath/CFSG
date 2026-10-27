
module

public import CFSG.Quasithin.Vol2.KGFactC31RuCand
import Certificates.Kernel.Misc.RuScan.Cand

public section

open CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31.Ru

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31.Ru in
theorem certificate7231 : ∀ i, 1 ≤ i → i < 4 → ∀ c ∈ ruC, cosetH i * c * ruZ * (cosetH i * c)⁻¹ ≠ ruZ →
    ∀ es q, (es, q) ∈ ruGroups → CandConcl i (cosetH i * c) ruZ es q :=
  fun _ _ hi _ hc hmv _ _ hes => KernelMisc.RuScan.candFactC hi hc hmv hes

end Certificates

end
