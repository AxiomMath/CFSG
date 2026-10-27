module

public import Certificates.Kernel.AE6Q8.Cls
public import Certificates.Kernel.AE6Q8.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Q8

open CFSG.KS CFSG.KC.Enum CFSG.KS.SporSch.MOC

theorem kPair : allN SR.R (pairK 360 9 (mask 9) (360 * 9) SC.BP 5 SC.LR SC.TR SR.RL SR.RC SR.RO
    SR.CT SR.QC SR.QJ SR.zc SR.nq) = true := by
  decide +kernel

theorem kSub : allN SR.nq (subK 360 9 (mask 9) (360 * 9) SC.BP 5 SK.N SK.ncl SC.LR SC.TR
    SK.E SR.RP SR.JO SR.CJ SR.X SR.XI SR.QC SR.QJ SR.QW) = true := by
  decide +kernel

end CertificateChecks.KernelAE6Q8

end
