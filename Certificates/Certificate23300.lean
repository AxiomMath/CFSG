module

public import Certificates.Data.SolMaxH35HS
import Certificates.Kernel.HS3850.SmallFacts

public section

namespace Certificates

open CFSG.ComponentClassification.SolMax.H35.HS in
theorem certificate23300 : hsH35Check = true := CFSG.KD.HS3850.hsH35Check_true

end Certificates
