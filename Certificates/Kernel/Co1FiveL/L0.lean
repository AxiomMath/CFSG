module

public import Certificates.Kernel.Co1FiveL.Data
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Data.Kernel.Co1LeafQ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1FiveL

open CFSG.KC.Co1LeafQ CFSG.KD.Co1FiveL

theorem kLeaf0 : leafQK CertificateChecks.KernelCo1B.Bound17591.XB BT0 E0 M0 U0 T0 IMS0 CL0 SL0 UIT0
    125 = true := by
  quickRfl

end CertificateChecks.KernelCo1FiveL

end
