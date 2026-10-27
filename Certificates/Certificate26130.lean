module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl2
import Certificates.Kernel.TwoHS.HarGlue

public section

namespace Certificates

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26130 : harModelOK = true ∧ harPOK = true ∧ harLiftOK = true := CFSG.KD.TwoHS.har_true

end Certificates
