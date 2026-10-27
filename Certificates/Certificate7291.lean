module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarCOdd
import Certificates.Kernel.TwoHS.HarCGlue

public section

namespace Certificates

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate7291 : harCOK () = true := CFSG.KD.TwoHS.harCOK_true

end Certificates
