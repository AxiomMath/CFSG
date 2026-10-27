module

public import Certificates.Kernel.CoreD2K.M24.Data
public import Certificates.Data.Kernel.CoreD2K.PairsZ
public import Certificates.Data.CoreD2Mathieu
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCoreD2K.M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CoreD2K
open Certificates.CoreD2Perm

@[expose] def m24V : VData := { base := m24CoreData, ys := [], gk := [], wAs := [], wBs := [] }

theorem k_sz : szOK 24 5 = true := by quickRfl
theorem k_gens : gensK 24 5 m24V GP GPI EG GT GTI = true := by quickRfl
theorem k_nab : nabK 24 5 m24CoreData.eW.length EG = true := by quickRfl
theorem k_cen : cenK 24 5 3 m24CoreData.eW.length EG = true := by quickRfl
theorem k_pairs : pairsZK 24 5 m24CoreData GP EG GT GTI = true := by quickRfl
theorem k_norm : normK 24 5 3 m24CoreData.eW.length EG 1 0 1 1 = true := by quickRfl

end CertificateChecks.KernelCoreD2K.M24
