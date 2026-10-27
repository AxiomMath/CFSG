module

public import Certificates.Kernel.A45Cls.Checks3

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.Certificates.Kernel.PkCV

theorem swK442017 : allN CA.N (fun i => strictB (CA.T i) fun u =>
    !invFixK 45 6 15 u || (cjAll 45 6 24 kaN kbN u && cjAll 45 6 24 kbN kaN u)) = true := by
  decide +kernel

end CertificateChecks.KernelA45

end
