module

public import Certificates.Kernel.Census.J2V.Data
public import Certificates.Data.Kernel.J2V
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelJ2V

open CFSG.KC.J2V

theorem comm_ok : commCheck (tabT vTt) (tabI vIt) vCommL = true := by quickRfl

theorem idx_ok : subIndexCheckWith (tabT vTt) (tabI vIt) (tabI vCut) vUsqt vCommL = true := by
  quickRfl

end CertificateChecks.KernelJ2V
