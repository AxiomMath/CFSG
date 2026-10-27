module

import Certificates.Kernel.TitsOver.Five.Over7088
public import CFSG.Quasithin.Recognition.RuRank3TitsClsBase

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.RuRank3 in
theorem certificate7088 : ∀ K : Subgroup (Equiv.Perm (Fin 1755)), K ≤ titsD → 25 ∣ Nat.card K →
    7800 ≤ Nat.card K → K ≠ titsD → ∃ d ∈ titsD, K = titsK0.map (MulAut.conj d).toMonoidHom := KernelTitsOver.Over7088.c7088

end Certificates
