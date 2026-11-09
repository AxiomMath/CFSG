module

public import Certificates.Kernel.AS91Sx.SxData
public import Certificates.Kernel.SporSch.Mathieu.GenBT
public meta import Certificates.Kernel.AS91Sx.SxData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAS91Sx.Sx664OC

meta def btHint : String := include_str "SxBT.txt"

end CertificateChecks.KernelAS91Sx.Sx664OC

#kss_bt CertificateChecks.KernelAS91Sx.Sx664B CertificateChecks.KernelAS91Sx.Sx664Q 24 5 6
  CertificateChecks.KernelAS91Sx.Sx664OC.btHint

end
