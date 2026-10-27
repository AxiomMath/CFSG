module

public import CFSG.Sporadic.J4.QTRankNative
import Certificates.Kernel.J4Q.C4024

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
theorem certificate4024 : (tabL.Nodup)
    ∧ (∀ t ∈ tabL, lenOK t = true)
    ∧ (idT ∈ tabL)
    ∧ (∀ t ∈ tabL, ∀ i < 4,
          compT t (kTab i) ∈ tabL ∧ compT t (kInvTab i) ∈ tabL)
    ∧ (∀ i < 4, lenOK (kTab i) = true ∧ lenOK (kInvTab i) = true)
    ∧ (∀ t ∈ tabL, compT t t = idT → t ≠ idT → fixCount t ≤ 128)
    ∧ (tabL.length = 1024)
    ∧ (∀ i < 4, ∀ ℓ ∈ kWords.getD i [], ℓ ∈ letters)
    ∧ (∀ ℓ ∈ letters, lenOK (letterTab ℓ) = true)
    ∧ (∀ e < 1024, ∀ i ∈ pcSeq e, i < 4) := KernelJ4Q.c4024

end Certificates
