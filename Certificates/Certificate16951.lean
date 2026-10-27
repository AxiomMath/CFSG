
module

public import Certificates.Certificate16951Base
import all Certificates.Certificate16951Base


public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section


namespace CertificateChecks.Batch16951

end CertificateChecks.Batch16951

namespace Certificates

open CertificateChecks

theorem certificate16951 : ((CFSG.Monster.B.TwoA.Co2Inv.dC : CFSG.Monster.Code.C) : Fin 24 → ZMod 2) ⬝ᵥ
    (Pi.single 0 1 + Pi.single 1 1) = 0 := by
  exact CertificateChecks.Batch16951.XQ_dC_mem_centralizer_0

end Certificates
