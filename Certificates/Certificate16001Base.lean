
module

public import CFSG.Monster.B.TwoA.Sp8.QuadInvInputs
public import Certificates.Data.BT2K1Vocab

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.Code

public section


open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.Code

namespace CertificateChecks.Batch16001

private theorem triM_qPoly_0 :
    ∀ v : Fin 8 → ZMod 2, qPoly (0 + ∑ j, v j • triM j) = qPoly v := by
  decide +kernel

end CertificateChecks.Batch16001

namespace Certificates

end Certificates
