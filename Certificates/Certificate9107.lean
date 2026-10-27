module

public import CFSG.Sporadic.Presentation.Fi22ExactData
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.Fi22F.Bound
import Certificates.Kernel.Fi22.Bridge

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Presentation CFSG.Sporadic.Presentation.Fi22Exact in
open CFSG.CosetTable in
theorem certificate9107 : (Finite (CFSG.CosetTable.PG 6 wsF) ∧ Nat.card (CFSG.CosetTable.PG 6 wsF) ≤ 774741019852800)
    ∧ (Finite TauCeti.SporadicName.Fi22.Group ∧
      Nat.card TauCeti.SporadicName.Fi22.Group ≤ 64561751654400) := ⟨KernelFi22F.card_le, KernelFi22.fi22⟩

end Certificates
