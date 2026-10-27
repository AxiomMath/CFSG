module

public import CFSG.LieType.Steinberg.Adjoint.CertInputs
import Certificates.Certificate113
import Certificates.Certificate114

public section

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

namespace CertificateChecks.Batch117

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley

namespace AVec

end AVec

namespace AdjData

variable {τ : Tag} (D : AdjData τ)

end AdjData

private theorem f4Data_checkTables : f4Data.checkTables = true := by decide +kernel
private theorem f4Data_checkSimple : f4Data.checkSimple = true := by decide +kernel
private theorem f4Data_checkWeyl : f4Data.checkWeyl = true := by decide +kernel
private theorem f4Data_checkPairs : f4Data.checkPairs = true := by decide +kernel
private theorem e8Data_checkTables : e8Data.checkTables = true := by decide +kernel
private theorem e8Data_checkSimple : e8Data.checkSimple = true := by decide +kernel
end CertificateChecks.Batch117

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint in
open CFSG.Blueprint.Chevalley in
theorem certificate117 : (f4Data.checkTables = true)
    ∧ (f4Data.checkSimple = true)
    ∧ (f4Data.checkWeyl = true)
    ∧ (f4Data.checkPairs = true)
    ∧ (e8Data.checkTables = true)
    ∧ (e8Data.checkSimple = true) := by
  exact ⟨CertificateChecks.Batch117.f4Data_checkTables, CertificateChecks.Batch117.f4Data_checkSimple, CertificateChecks.Batch117.f4Data_checkWeyl, CertificateChecks.Batch117.f4Data_checkPairs, CertificateChecks.Batch117.e8Data_checkTables, CertificateChecks.Batch117.e8Data_checkSimple⟩

end Certificates
