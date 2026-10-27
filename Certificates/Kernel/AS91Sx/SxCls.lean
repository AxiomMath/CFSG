module

public import Certificates.Kernel.AS91Sx.SxData
public import Certificates.Kernel.SporSch.Mathieu.Gen3
public meta import Certificates.Kernel.AS91Sx.SxData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_classes2 CertificateChecks.KernelAS91Sx.Sx664CK 24 5 CertificateChecks.KernelAS91Sx.Sx664OC.tAM
  CertificateChecks.KernelAS91Sx.Sx664OC.tBM CertificateChecks.KernelAS91Sx.Sx664OC.tA
  CertificateChecks.KernelAS91Sx.Sx664OC.tB CertificateChecks.KernelAS91Sx.Sx664OC.repsM 5 40000

end
