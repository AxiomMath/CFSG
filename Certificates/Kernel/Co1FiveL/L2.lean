module

public import Certificates.Kernel.Co1FiveL.Data
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Data.Kernel.Co1LeafQ
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1FiveL

open CFSG.KC.Co1LeafQ CFSG.KD.Co1FiveL

theorem kLeaf2 : leafQK CertificateChecks.KernelCo1B.Bound17591.XB BT2 E2 M2 U2 T2 IMS2 CL2 SL2 UIT2
    250 = true := by
  quickRfl

end CertificateChecks.KernelCo1FiveL

end
