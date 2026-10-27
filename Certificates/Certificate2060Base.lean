
module

public import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Certificates.Kernel.SporSch.Co2SShapeSound
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

namespace Certificates

open CFSG.KS.Co2SShape CFSG.Sporadic.Co2Schreier

set_option maxRecDepth 100000 in
theorem localShapeK_rec : localShapeK localRec = true := by quickRfl

end Certificates
