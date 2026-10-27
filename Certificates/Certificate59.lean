module

public import CFSG.LieType.Chevalley.RootOps.Cover
public import CFSG.LieType.Chevalley.RootOps.Data.E8Comm
import Certificates.Certificate113
import Certificates.Certificate114
import Certificates.Certificate46
import Certificates.Certificate47
import Certificates.Certificate48
import Certificates.Certificate50
import Certificates.Certificate51
import Certificates.Certificate52
import Certificates.Certificate54
import Certificates.Certificate55
import Certificates.Certificate56
import Certificates.Certificate57
import Certificates.Certificate58
import Certificates.Certificate60
import Certificates.Certificate61
import Certificates.Certificate62
import Certificates.Certificate63
import Certificates.Certificate64
import Certificates.Certificate65
import Certificates.Certificate66
import Certificates.Certificate67
import Certificates.Certificate69
import Certificates.Certificate70
import Certificates.Certificate71
import Certificates.Certificate73
import Certificates.Certificate74
import Certificates.Certificate75

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch59

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem e8_repsCheck : repsCheck .E8 e8Reps = true := by decide +kernel

private theorem e8_coverCheck : coverCheck .E8 e8Reps e8Cover = true := by decide +kernel

end CertificateChecks.Batch59

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate59 : (repsCheck .E8 e8Reps = true)
    ∧ (coverCheck .E8 e8Reps e8Cover = true) := by
  exact ⟨CertificateChecks.Batch59.e8_repsCheck, CertificateChecks.Batch59.e8_coverCheck⟩

end Certificates
