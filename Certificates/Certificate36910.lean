module

public import Certificates.Certificate1020
public import Certificates.Certificate1021
public import Certificates.Certificate16949
import Certificates.Kernel.ThPump.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance in
theorem certificate36910 : ∀
    {t : CFSG.Sporadic.Th.J},
    orderOf t = 3 → t * ThList.c5 = ThList.c5 * t →
    Nat.card ↥(Subgroup.centralizer ({ThList.c5} : Set CFSG.Sporadic.Th.J) ⊓
      Subgroup.centralizer ({t} : Set CFSG.Sporadic.Th.J)) ≤ 30 :=
  fun ht3 htc => KernelThPump.thPump_kernel ht3 htc

end Certificates
