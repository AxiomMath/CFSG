module

public import CFSG.Sporadic.Presentation.McLExactDataInputs
import Certificates.Kernel.McL.Bridge
public import CFSG.Sporadic.Presentation.Common

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Presentation CFSG.Sporadic.Presentation.McL in
open CFSG.CosetTable in
theorem certificate9126 : Finite TauCeti.SporadicName.McL.Group ∧
    Nat.card TauCeti.SporadicName.McL.Group ≤ 898128000 := KernelMcL.mcl

end Certificates
