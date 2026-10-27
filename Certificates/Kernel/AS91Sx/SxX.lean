module

public import Certificates.Kernel.AS91Sx.SxData
public import Certificates.Kernel.SporSch.Mathieu.Gen2
public meta import Certificates.Kernel.AS91Sx.SxData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_cntord2 CertificateChecks.KernelAS91Sx.Sx664X CertificateChecks.KernelAS91Sx.Sx664Q 24 5
  CertificateChecks.KernelAS91Sx.Sx664OC.SM CertificateChecks.KernelAS91Sx.Sx664OC.baseM
  CertificateChecks.KernelAS91Sx.Sx664OC.One CertificateChecks.KernelAS91Sx.Sx664OC.oneM 5

end
