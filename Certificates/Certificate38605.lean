module

public import Certificates.Data.SmithL6Aut
import CFSG.Certificates.Kernel.SmithL6DualSound
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CertificateChecks.Batch38605

private theorem ch38605 : CFSG.KC.SmithL6D.dualK CFSG.SmithL6.wData.toList = true := by
  quickRfl

private theorem swapPlanesCheck_holds_0 : CFSG.SmithL6.chkSwapPlanes = true :=
  CFSG.KC.SmithL6D.chkSwapPlanes_of ch38605

end CertificateChecks.Batch38605

namespace Certificates

open CertificateChecks

theorem certificate38605 : CFSG.SmithL6.chkSwapPlanes = true := CertificateChecks.Batch38605.swapPlanesCheck_holds_0

end Certificates
