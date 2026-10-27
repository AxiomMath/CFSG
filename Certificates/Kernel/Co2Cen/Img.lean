module

public import Certificates.Kernel.Co2Cen.Data
public import Certificates.Kernel.Co2Cen.ImgData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Cen

open CFSG.KC.Co2Cen

theorem img1 : treeNK PE1 PM1 PS1 PT1 MK1 128 = true := by quickRfl

theorem img8 : treeNK PE8 PM8 PS8 PT8 MK8 16 = true := by quickRfl

end CertificateChecks.KernelSpor.Co2Cen

end
