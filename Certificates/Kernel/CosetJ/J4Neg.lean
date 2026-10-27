module

public import Certificates.Kernel.CosetJ.J4Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCosetJ.J4.Neg

open CFSG.Sporadic.J4Schreier CFSG.Sporadic.Recognition.J4Multiplier CFSG.KC.CosetJ.F2
open CertificateChecks.KernelCosetJ.J4

theorem form_noS3 : (formOK j4cSsym.toList j4cSdiag.toList [] j4cSB.toList xColumns.toList
    yColumns.toList).not = true := by quickRfl

theorem form_swap : (formOK j4cSsym.toList j4cSdiag.toList j4cSA.toList j4cSB.toList
    yColumns.toList xColumns.toList).not = true := by quickRfl

theorem fox_noX :
    (foxOK [] j4FoxY.toList xColumns.toList yColumns.toList ws).not = true := by quickRfl

theorem fox_noWord :
    (foxOK j4FoxX.toList j4FoxY.toList xColumns.toList yColumns.toList ws.tail).not = true := by
  quickRfl

end CertificateChecks.KernelCosetJ.J4.Neg

end
