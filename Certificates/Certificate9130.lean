module

public import CFSG.Sporadic.Presentation.SuzInputs
import Certificates.Kernel.Bounds.Bridge

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Presentation.Suz CFSG.CosetTable in
theorem certificate9130 : (Finite TauCeti.SporadicName.Suz.Group ∧
      Nat.card TauCeti.SporadicName.Suz.Group ≤ 448345497600) ∧
    (Finite (PG _ R1) ∧ Nat.card (PG _ R1) ≤ 251596800) :=
  ⟨KernelBounds.suz, KernelBounds.suzR1⟩

end Certificates
