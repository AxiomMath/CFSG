module

public import CFSG.Sporadic.Th.Setup
public import Certificates.Certificate1022
import Certificates.Kernel.ThDemp.OrbAssembly
import CFSG.Sporadic.Th.Certificate
import Certificates.Certificate1021
import CFSG.Sporadic.Th.CertificateBase
import CFSG.Sporadic.Th.CertificateBase1
import CFSG.Sporadic.ThSchreier.KernelAut
import CFSG.Sporadic.ThSchreier.KernelAutBase
import CFSG.Sporadic.ThSchreier.KernelAutBase1

public section

namespace Certificates

open CertificateChecks

theorem certificate17400 : ∃ x : CFSG.Sporadic.Th.J, orderOf x = 31 ∧
    Nat.card (Subgroup.centralizer ({x} : Set CFSG.Sporadic.Th.J)) ≤ 31 := by
  obtain ⟨-, ⟨x, -, hx, hc⟩⟩ := KernelThDemp.th_centralizer_bounds
    (CFSG.Sporadic.Th.Kernel.card_J_eq th_kernel_facts_ok).le
  exact ⟨x, hx, hc⟩

end Certificates
