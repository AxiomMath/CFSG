module

import Certificates.Kernel.SporSch.PairBT.McLF67Facts
public import CFSG.Sporadic.Schreier.PairMcLCertBase

public section

namespace Certificates

open CertificateChecks

theorem certificate5196 : ∀ (r s : ℕ) (a b y : ↥CFSG.Sporadic.Schreier.mclP), r.Prime → s.Prime → Odd r → Odd s →
    r ≠ s → a ^ r = 1 → b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 →
    a * b = b * a → a * y = y * a → b * y = y * b → False := KernelSporSch.McLF67.triples_mclP

end Certificates
