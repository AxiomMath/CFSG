module

public import Certificates.Certificate664011

public section

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Th.Native

theorem sx_schreier :
    sxCert.check = true ∧ sxCert.orderCertificate = 138240 :=
  Certificates.certificate664011.1

theorem sx_center : sxCenterOK = true :=
  Certificates.certificate664011.2.1

theorem sx_aut_orders :
    ordTest 24 5 (toTable sxA) = true ∧ ordTest 24 4 (toTable sxB) = true := by
  simpa only [sxAT_eq, sxBT_eq] using Certificates.certificate664011.2.2.1

theorem sx_aut_words :
    wordsTest 24 5 4 sxAutWords (toTable sxA) (toTable sxB) = true := by
  simpa only [sxAT_eq, sxBT_eq] using Certificates.certificate664011.2.2.2.1

theorem sx_aut_reps :
    repsOK 24 (pairTables sxA sxB) (pairTables sxA⁻¹ sxB⁻¹)
        (cosetOrderTables sxCert 1 5) [toTable sxA] 40000 = true ∧
      repsTotal 24 (pairTables sxA sxB) (pairTables sxA⁻¹ sxB⁻¹) [toTable sxA]
          (orderTables sxCert 4) 40000 (wordsTest 24 5 4 sxAutWords) = 138240 := by
  simpa only [sxAT_eq, sxBT_eq] using Certificates.certificate664011.2.2.2.2

end CFSG.Quasithin.H13.AS91.M24G
