module

public import Certificates.Kernel.Co1ThreeK.DataP
import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.Co1ThreeK.GenQ

public section

set_option maxRecDepth 400000 in
#kc_eval CertificateChecks.KernelCo1ThreeK FM CertificateChecks.KernelCo1ThreeK.GenQ.qStep
  CS.TR CS.NR CS.Q CS.W

end
