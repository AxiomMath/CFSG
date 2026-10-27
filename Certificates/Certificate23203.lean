module

public import Certificates.Data.FooteLitCF23HSCheck
import Certificates.Kernel.HS3850.FusFacts

public section

namespace Certificates

open CFSG.ComponentClassification.GSThmB.CF23I.HS in
theorem certificate23203 : hsFusOK = true := CFSG.KD.HS3850.hsFusOK_true

end Certificates
