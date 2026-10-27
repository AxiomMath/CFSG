module

public import CFSG.Sporadic.Presentation.ONanInputs
import Certificates.Kernel.Bounds.ONBridge
import Certificates.Kernel.Bounds.ONR1Bridge

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.Sporadic.Presentation.ONan in
theorem certificate9127 : (Finite TauCeti.SporadicName.ONan.Group ∧
    Nat.card TauCeti.SporadicName.ONan.Group ≤ 460815505920) ∧
    (Finite (PG _ R1) ∧ Nat.card (PG _ R1) ≤ 3753792) := ⟨KernelBounds.onan, KernelBounds.onanR1⟩

end Certificates
