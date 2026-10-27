module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.Co1M.G16956

public section

namespace Certificates

open CertificateChecks

theorem certificate16956 : ∀ x : CFSG.Blueprint.NativeSporadic.Co1, orderOf x = 13 →
    Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1)) = 156 ∧
      ∀ g ∈ Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1),
        ∀ z ∈ Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1),
          orderOf z = 3 → g * z * g⁻¹ ∈ Subgroup.zpowers z → g ^ 39 = 1 := KernelCo1M.co1_thirteen_k

end Certificates
