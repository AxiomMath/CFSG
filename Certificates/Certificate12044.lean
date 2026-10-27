module

public import CFSG.LieType.Multipliers.G24Data
import Certificates.Kernel.Misc.G24Facts

public section

namespace Certificates

open CFSG.LieType.Multipliers.G24 in
theorem certificate12044 :
    (invCheck = true)
    ∧ (relCheck = true)
    ∧ (commCheck = true)
    ∧ (rootCheck = true)
    ∧ (suzCheck = true) := CFSG.KD.Misc.G24.facts44

end Certificates
