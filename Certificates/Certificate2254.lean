
module


public import CFSG.Sporadic.Schreier.RuOrbLFacts
import Certificates.Kernel.SporSch.Ru.LA2254Facts
import Certificates.Kernel.SporSch.Ru.LB2255Data

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.RuSchreier in
theorem certificate2254 : 
    (∀ i < 3, ruZL i ∈ Subgroup.centralizer (ruL : Set (Equiv.Perm (Fin 4060)))) ∧
      ∀ k < 19, ∀ k' < 19, k ≠ k' → Disjoint (ruOrb k) (ruOrb k') :=
  ⟨fun _ hi => KernelSporSch.RuLA.ruZL_central hi,
    fun _ hk _ hk' h => KernelSporSch.RuLA.ruOrb_disjoint hk hk' h⟩

end Certificates
