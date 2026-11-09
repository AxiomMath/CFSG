module

public import Certificates.Kernel.AS91Sx.SxCls
public import Certificates.Kernel.SporSch.Mathieu.GenBT
public meta import Certificates.Kernel.AS91Sx.SxData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAS91Sx.Sx664OC

meta def btHint : String := include_str "Sx664BT.txt"

end CertificateChecks.KernelAS91Sx.Sx664OC

#kss_bt CertificateChecks.KernelAS91Sx.Sx664BC CertificateChecks.KernelAS91Sx.Sx664Q 24 5 6
  CertificateChecks.KernelAS91Sx.Sx664OC.btHint

#kss_zscan CertificateChecks.KernelAS91Sx.Sx664ZA CertificateChecks.KernelAS91Sx.Sx664BC
  CertificateChecks.KernelAS91Sx.Sx664CK 24 5 CertificateChecks.KernelAS91Sx.Sx664OC.btHint
  CertificateChecks.KernelAS91Sx.Sx664OC.tAM
  CertificateChecks.KernelAS91Sx.Sx664OC.tBM CertificateChecks.KernelAS91Sx.Sx664OC.repsM
  CFSG.Quasithin.H13.AS91.M24G.sxAutWords 5 4 12

end
