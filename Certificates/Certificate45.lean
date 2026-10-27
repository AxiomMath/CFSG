module

public import CFSG.LieType.Chevalley.RootOps.Cover
public import CFSG.LieType.Chevalley.RootOps.Data.D4Comm
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

namespace CertificateChecks.Batch45

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem d4_repsCheck : repsCheck .D4 d4Reps = true := by decide +kernel

private theorem d4_coverCheck : coverCheck .D4 d4Reps d4Cover = true := by decide +kernel

end CertificateChecks.Batch45

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate45 : (repsCheck .D4 d4Reps = true)
    ∧ (coverCheck .D4 d4Reps d4Cover = true) := by
  exact ⟨CertificateChecks.Batch45.d4_repsCheck, CertificateChecks.Batch45.d4_coverCheck⟩

end Certificates
