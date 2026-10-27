module

public import Certificates.Kernel.CoreD2K.Tits.Data
public import Certificates.Data.Kernel.CoreD2K.Pairs
public import Certificates.Data.CoreD2Tits
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 10

namespace CertificateChecks.KernelCoreD2K.Tits

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CoreD2K
open Certificates.CoreD2Perm

@[expose] def titsV : VData := { base := titsData, ys := [], gk := [], wAs := [], wBs := [] }

theorem k_sz : szOK 1755 11 = true := by quickRfl
theorem k_gens : gensK 1755 11 titsV GP GPI EG GT GTI = true := by quickRfl
theorem k_pairs : pairsK 1755 11 titsData GP EG GT GTI = true := by quickRfl
theorem k_norm : normK 1755 11 3 titsData.eW.length EG 1 0 1 1 = true := by quickRfl

end CertificateChecks.KernelCoreD2K.Tits

end
