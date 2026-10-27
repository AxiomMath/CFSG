
module

public import Certificates.Certificate8072Base
import all Certificates.Certificate8072Base

public import Certificates.Certificate2264

public section

set_option maxRecDepth 400000

open CFSG CFSG.Quasithin CFSG.KC.TitsBridge CFSG.KC.Enum CFSG.KS

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native in
theorem certificate8072 : (titsArray CFSG.Open.quasithinTitsData1 = CFSG.Sporadic.Schreier.Tits.titsDerivedArrs[0]!)
    ∧ (titsArray CFSG.Open.quasithinTitsData2 = CFSG.Sporadic.Schreier.Tits.titsDerivedArrs[1]!) := by
  exact ⟨CertificateChecks.Batch8072.titsBridge_array₁_0, CertificateChecks.Batch8072.titsBridge_array₂_1⟩

end Certificates

end
