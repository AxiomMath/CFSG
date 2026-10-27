module

public import Certificates.Kernel.Co2JRank.Data
public import Certificates.Kernel.Co2J.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2JRank

open CFSG.KC.Loop CFSG.KC.Co2JRank

theorem ranks :
    allBelow 1024 16 (fun v => ptJ CR K1 K3 (Co2J.GJ 8) 256 (Co2J.JE v) v) = true := by
  quickRfl

theorem tab : tabJ K1 K3 256 CNT OM OL 77 NT W5 W3 C = true := by quickRfl

end CertificateChecks.KernelSpor.Co2JRank

end
