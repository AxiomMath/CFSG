module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl2
import Certificates.Kernel.TwoHS.FourGlue

public section

namespace Certificates

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26133 : harFourOK 0 = true ∧ harFourOK 1 = true := CFSG.KD.TwoHS.harFourOK_true

end Certificates
