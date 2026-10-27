module

public import CFSG.YGroups.DCE.B433Y333
import Certificates.Kernel.B433Alt.Y333B

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups CFSG.YGroups.DCE.B433 in
theorem certificate9355 : J432.index ≤ 31671 ∧
    (4154781481226426191177580544000000 ≤ Nat.card B433 → 153064959367549707878400 ≤ Nat.card P333) :=
  ⟨by rw [← KernelB433.lsub_tL_eq]; exact KernelY442.index_tL_le.2, KernelB433.card_P333_ge⟩

end Certificates
