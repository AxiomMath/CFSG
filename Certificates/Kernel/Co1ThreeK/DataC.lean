module

public import Certificates.Kernel.Co1ThreeK.DataP
import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.Co1ThreeK.GenC

public section

set_option maxRecDepth 400000 in
#kc_eval CertificateChecks.KernelCo1ThreeK CB CertificateChecks.KernelCo1ThreeK.GenC.cStep CS.TR

end
