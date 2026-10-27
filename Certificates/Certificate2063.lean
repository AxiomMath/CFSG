module

public import CFSG.Sporadic.Co2Schreier.WitCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.WitText
public import CFSG.Certificates.Kernel.SporSch.Co2SShapeSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CFSG.KS.Co2SShape CFSG.Sporadic.Co2Schreier

set_option maxRecDepth 100000 in
theorem witShapeK_rec : witShapeK witRec = true := by quickRfl

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier in
theorem certificate2063 : witShapeOK witRec = true := witShapeK_sound witShapeK_rec

end Certificates
