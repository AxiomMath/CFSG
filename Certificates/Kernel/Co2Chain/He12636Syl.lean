module

public import Certificates.Kernel.Co2Chain.He12636SylData
public import Certificates.Kernel.Co2Chain.He12636Data
public import Certificates.Data.Kernel.SporSch.HeSyl
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Chain.He12636Syl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.HeCn CertificateChecks.KernelCo2Chain
open CertificateChecks.KernelSpor CFSG.Sporadic.HeldB

theorem kVal : sylValB (nfValidK 5 HeC.LR) 27 NF CJ = true := by quickRfl
theorem kRng : sylRngB 27 MT PAR GEN GI R = true := by quickRfl
theorem kMul0 : sylMulB HeTc.nfp heBase 27 NF MT GI 0 = true := by quickRfl
theorem kMul1 : sylMulB HeTc.nfp heBase 27 NF MT GI 1 = true := by quickRfl
theorem kMul2 : sylMulB HeTc.nfp heBase 27 NF MT GI 2 = true := by quickRfl
theorem kRoot : sylRootB HeTc.nfp heBase NF R = true := by quickRfl
theorem kKey : sylKeyB HeTc.nfp heBase 26 NF = true := by quickRfl
theorem kTree : sylTreeB 27 MT PAR GEN DEP R = true := by quickRfl
theorem kConj : sylConjB HeTc.nfp heBase (pmR H36RYA) (pmR H36RYB) 27 NF CJ CL R = true := by
  quickRfl

end CertificateChecks.KernelCo2Chain.He12636Syl

end
