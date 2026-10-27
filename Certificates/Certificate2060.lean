
module

public import Certificates.Certificate2060Base

public import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Certificates.Kernel.SporSch.Co2SShapeSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CFSG.KS.Co2SShape CFSG.Sporadic.Co2Schreier

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier in
theorem certificate2060 : localShapeOK localRec = true := localShapeK_sound localShapeK_rec

end Certificates
