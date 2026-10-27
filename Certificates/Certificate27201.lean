module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HSFixNsData
import Certificates.Kernel.HS3850.Ns27201Facts

public section

namespace Certificates

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate27201 : hnsOK = true := CFSG.KD.HS3850.hnsOK_true

end Certificates
