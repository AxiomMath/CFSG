module

public import CFSG.HardMathSupport.Foote.E27.SporJ3Data
public meta import CFSG.HardMathSupport.Foote.E27.SporJ3Data
import Certificates.Kernel.E27J3Syl.Glue

public section

namespace Certificates

open CFSG.HardMathSupport.Foote.E27 in
theorem certificate131001 : j3SylOK = true := CFSG.KD.E27J3S.j3SylOK_true

end Certificates
