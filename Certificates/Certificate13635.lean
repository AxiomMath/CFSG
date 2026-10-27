module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeInputs
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeInputs
import Certificates.Kernel.Co3T.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T in
theorem certificate13635 : qCheck () = true ∧ dCheck () = true ∧ hypCheck () = true ∧ fusCheck () = true ∧
    transCheck () = true ∧ cCheck () = true ∧ classCheck () = true := KernelCo3T.facts

end Certificates
