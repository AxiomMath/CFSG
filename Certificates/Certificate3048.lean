module

public import CFSG.Monster.B.Dyadic.Max2K
public import CFSG.Monster.B.Dyadic.PinnedK
import Certificates.Kernel.BabyMonster.Pair.Max2C
import Certificates.Kernel.BabyMonster.Pair.Pinned

public section

namespace Certificates

open CertificateChecks

theorem certificate3048 : CFSG.Monster.B.Dyadic.FactMax2 ∧ CFSG.Monster.B.Dyadic.FactPinned :=
  ⟨KernelBM.Pair.factMax2_of,
    KernelBM.Pair.factPinned⟩

end Certificates
