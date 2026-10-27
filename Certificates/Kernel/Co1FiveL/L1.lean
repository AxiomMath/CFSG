module

public import Certificates.Kernel.Co1FiveL.Data
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Data.Kernel.Co1LeafQ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1FiveL

open CFSG.KC.Co1LeafQ CFSG.KD.Co1FiveL

theorem kLeaf1 : leafQK CertificateChecks.KernelCo1B.Bound17591.XB BT1 E1 M1 U1 T1 IMS1 CL1 SL1 UIT1
    1500 = true := by
  quickRfl

end CertificateChecks.KernelCo1FiveL

end
