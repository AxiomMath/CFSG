module

public import Certificates.Kernel.SmithD6T2.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate38704 : ∀ p w : Nat, p < 4096 → p ≠ 0 → CFSG.SmithD6.qf p = false → w < 4096 →
    CFSG.SmithD6.bf p w = false → CFSG.SmithD6.qf w = true →
    ∃ s < 4096, s ≠ 0 ∧ CFSG.SmithD6.qf s = false ∧ CFSG.SmithD6.bf p s = false ∧
      CFSG.SmithD6.bf w s = true :=
  fun _ _ hp hp0 hpq hw hpw hwq => SmithD6T2.split_codes hp hp0 hpq hw hpw hwq

end Certificates
