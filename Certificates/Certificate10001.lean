module

public import CFSG.LargeExtraspecial.O62Check
import Certificates.Kernel.Misc.O62.Facts
import Certificates.Kernel.Misc.O62.Data
import CFSG.LargeExtraspecial.O62Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace Certificates

open CFSG.LargeExtraspecial.O62.Check in
theorem certificate10001 :
    (checkSylow false = true)
    ∧ (checkSylow true = true)
    ∧ (checkRank false = true)
    ∧ (checkRank true = true)
    ∧ (checkWC false = true)
    ∧ (checkWC true = true) := CFSG.KD.Misc.O62.facts

end Certificates
