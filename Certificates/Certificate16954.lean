module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.Co1M.G16954

public section

namespace Certificates

open CertificateChecks

theorem certificate16954 : ∀ x : CFSG.Blueprint.NativeSporadic.Co1, orderOf x = 11 →
    Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1)) ≤ 66 ∧
      3 ∣ Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1)) := KernelCo1M.co1_eleven_k

end Certificates
