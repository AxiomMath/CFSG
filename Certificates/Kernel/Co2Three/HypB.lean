module

public import Certificates.Kernel.Co2Three.K
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCo2Three

open CFSG.KC.Enum

@[expose] noncomputable def hypBd (ρ : ℕ) : ℕ := nIf(Nat.beq ρ 1, 81, 162)

@[expose] noncomputable def ch13636HypB (ρ : ℕ) : Bool := Nat.ble (hypS ρ) (hypBd ρ)

end CertificateChecks.KernelCo2Three

#kc_each CertificateChecks.KernelCo2Three.ch13636HypB 0 8

namespace CertificateChecks.KernelCo2Three

#kc_forall_chunks ch13636HypB_all (fun ρ => ch13636HypB ρ = true) 8
  CertificateChecks.KernelCo2Three.ch13636HypB 1

end CertificateChecks.KernelCo2Three

end
