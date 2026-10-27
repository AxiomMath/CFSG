module

public import Certificates.Kernel.AxisPlane.Cmd
public import Certificates.Kernel.AxisPlane.Cover.Data

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAP.Cover

#kc_planes CertificateChecks.KernelAP.Cover R3 lams3 sizes3 rowsA3 rowsB3
#kc_planes CertificateChecks.KernelAP.Cover R4 lams4 sizes4 rowsA4 rowsB4
#kc_planes CertificateChecks.KernelAP.Cover R5 lams5 sizes5 rowsA5 rowsB5

end CertificateChecks.KernelAP.Cover

end
