module

public import Certificates.Kernel.CoreD2K.M12.Data
public import Certificates.Data.Kernel.CoreD2K.Pairs
public import Certificates.Data.CoreD2Mathieu
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCoreD2K.M12

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CoreD2K
open Certificates.CoreD2Perm

@[expose] def m12V : VData := { base := m12CoreData, ys := [], gk := [], wAs := [], wBs := [] }

theorem k_sz : szOK 12 4 = true := by quickRfl
theorem k_gens : gensK 12 4 m12V GP GPI EG GT GTI = true := by quickRfl
theorem k_pairs : pairsK 12 4 m12CoreData GP EG GT GTI = true := by quickRfl
theorem k_norm : normK 12 4 3 m12CoreData.eW.length EG 1 0 2 1 = true := by quickRfl

end CertificateChecks.KernelCoreD2K.M12
