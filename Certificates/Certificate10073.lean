
module


public import Certificates.Kernel.Co1M.C73

public section

namespace Certificates

open CertificateChecks.KernelCo1M

open CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Odd CFSG.Sporadic.Co1.OddNative
  CFSG.Sporadic.SmallF2.Native in
theorem certificate10073 :
    (validOK = true)
    ∧ (fixOK = true)
    ∧ (partnerOK = true)
    ∧ (conjOK = true)
    ∧ (fixOK₂ = true)
    ∧ (pairFixOK 0 1024 405 = true)
    ∧ (pairFixOK 1 256 135 = true)
    ∧ (pairFixOK 2 256 75 = true)
    ∧ (gramOK (transposeRows 24 f0Rows) (Wk 1) = true)
    ∧ (gramOK (transposeRows 24 f0Rows) (Wk 2) = true)
    ∧ ∃ W : OddW, OddOK W :=
  ⟨c73_valid, c73_fix, c73_partner, c73_conj, c73_fix2, c73_pair0, c73_pair1, c73_pair2,
    c73_gram1, c73_gram2, w73, ok73⟩

end Certificates
