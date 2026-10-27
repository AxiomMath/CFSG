
module

public import Certificates.Certificate16001Base
import all Certificates.Certificate16001Base


public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.Code

public section


open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.Code

namespace CertificateChecks.Batch16001

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.Code

end CertificateChecks.Batch16001

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.Code in
theorem certificate16001 : ∀ v : Fin 8 → ZMod 2, qPoly (0 + ∑ j, v j • triM j) = qPoly v := by
  exact CertificateChecks.Batch16001.triM_qPoly_0

end Certificates
