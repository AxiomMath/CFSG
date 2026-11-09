
module

public import Certificates.Data.Kernel.Census.CatFacts.C2009Defs
public import Certificates.Data.Kernel.Census.CatFacts.C2009Orb
import Certificates.Kernel.Census.CatFacts.C2009L

public section

set_option maxHeartbeats 0

namespace CertificateChecks.KernelCatFacts

open CFSG.Certificates.Kernel.CatFacts CFSG.Certificates.Kernel.PkEnum
  CFSG.ComponentClassification.CatFactsSmall.PSp43

theorem nA2009K : ((transL QA45).headD []).length = 45 := by
  rw [← tAL_eq]
  decide +kernel

theorem sylLen2009K : ((elemsV cfQR).filter siftPQ).length = 64 := by decide +kernel

end CertificateChecks.KernelCatFacts

namespace CFSG.Certificates.Kernel.CatFacts

theorem orbChkTZ_ok : orbChkTZ = true := by decide +kernel

theorem orbChkZ_ok : orbChkZ = true := by decide +kernel

theorem orbTZK_nodup : orbTZK.Nodup := by decide +kernel

theorem orbZK_nodup : orbZK.Nodup := by decide +kernel

theorem sylChk2009_ok : sylChk2009 = true := by decide +kernel

end CFSG.Certificates.Kernel.CatFacts
