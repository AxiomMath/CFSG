module

import Certificates.Kernel.SporSch.PairBT.J3F67Facts
public import CFSG.Sporadic.Schreier.PairJ3CertBase

public section

namespace Certificates

open CertificateChecks

theorem certificate5195 : ∀ (r s : ℕ) (a b y : ↥CFSG.Sporadic.Schreier.j3P), r.Prime → s.Prime → Odd r → Odd s →
    r ≠ s → a ^ r = 1 → b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 →
    a * b = b * a → a * y = y * a → b * y = y * b → False := KernelSporSch.J3F67.triples_j3P

end Certificates
