module

public import CFSG.LieType.Multipliers.G23Data
import Certificates.Kernel.Misc.G23Facts

public section

namespace Certificates

open CFSG.LieType.Multipliers.G23 in
theorem certificate12043 : CFSG.LieType.Multipliers.G23.coverCheck = true ∧ relSixCheck = true := CFSG.KD.Misc.G23.facts

end Certificates
