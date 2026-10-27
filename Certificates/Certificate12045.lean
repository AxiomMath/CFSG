module

public import CFSG.LieType.Multipliers.G24Data
import Certificates.Kernel.Misc.G24Facts

public section

namespace Certificates

open CFSG.LieType.Multipliers.G24 in
theorem certificate12045 :
    (unitCheck = true)
    ∧ (coverCheck = true)
    ∧ (kerCheck = true) := CFSG.KD.Misc.G24.facts45

end Certificates
