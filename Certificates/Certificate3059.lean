
module

public import Certificates.Certificate3059Base


public section

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Co2

namespace CertificateChecks.Batch3059

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Co2

end CertificateChecks.Batch3059

namespace Certificates

open CertificateChecks.Batch3059 in
open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Co2 in
theorem certificate3059 : (∀ t < 22, rImg[t]! = (cRows 9)[t]! ^^^ 2 ^ t)
    ∧ (∀ t < 22, Native.actD 6 zBasis
       ([0, 2, 2, 2, 2, 2, 4, 14, 38, 0, 0, 23, 23, 23, 23, 23, 23, 22, 22, 22, 22, 22].getD t 0) =
         rImg[t]!)
    ∧ (∀ t : Fin 6, Native.actD 22 rImg
       ([133120, 2, 64, 194, 131138, 322].getD t 0) = zBasis[(t : ℕ)]!) :=
  ⟨rImg_spec, rImg_comb, zBasis_rComb⟩

end Certificates
