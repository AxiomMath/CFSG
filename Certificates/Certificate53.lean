module

public import CFSG.LieType.Chevalley.RootOps.Cover
public import CFSG.LieType.Chevalley.RootOps.Data.E7Comm
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

namespace CertificateChecks.Batch53

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem e7_repsCheck : repsCheck .E7 e7Reps = true := by decide +kernel

private theorem e7_coverCheck : coverCheck .E7 e7Reps e7Cover = true := by decide +kernel

end CertificateChecks.Batch53

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate53 : (repsCheck .E7 e7Reps = true)
    ∧ (coverCheck .E7 e7Reps e7Cover = true) := by
  exact ⟨CertificateChecks.Batch53.e7_repsCheck, CertificateChecks.Batch53.e7_coverCheck⟩

end Certificates
