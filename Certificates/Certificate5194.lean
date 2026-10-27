module

import Certificates.Kernel.SporSch.PairBT.J2F67Facts
public import CFSG.Sporadic.Schreier.PairJ2CertBase
public import Certificates.Certificate2233Base

public section

namespace Certificates

open CertificateChecks

theorem certificate5194 : ∀ (r s : ℕ) (a b y : ↥CFSG.Sporadic.Schreier.j2P), r.Prime → s.Prime → Odd r → Odd s →
    r ≠ s → a ^ r = 1 → b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 →
    a * b = b * a → a * y = y * a → b * y = y * b → False := KernelSporSch.J2F67F.triples_j2P

end Certificates
