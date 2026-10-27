module

public import Certificates.Data.ONanF2Facts
import Certificates.Kernel.ONanF2.Glue

public section

namespace Certificates

open CFSG.OddStandard.ONanRec.F2 in
theorem certificate6142 : f2Check = true := CFSG.KC.ONanF2.Glue.f2Check_true

end Certificates
