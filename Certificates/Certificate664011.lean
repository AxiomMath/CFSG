module

public import CFSG.Quasithin.H13.AS91Sec8V1AutData
public meta import CFSG.Quasithin.H13.AS91Sec8V1AutData
import Certificates.Kernel.AS91Sx.SxFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native in
open CFSG.Sporadic.Th.Native CFSG.Quasithin.H13.AS91.M24G in
theorem certificate664011 :
    (sxCert.check = true ∧ sxCert.orderCertificate = 138240)
    ∧ (sxCenterOK = true)
    ∧ (ordTest 24 5 (toTable sxAT) = true ∧ ordTest 24 4 (toTable sxBT) = true)
    ∧ (wordsTest 24 5 4 sxAutWords (toTable sxAT) (toTable sxBT) = true)
    ∧ (CFSG.Sporadic.Schreier.Native.repsOK 24 (pairTables sxAT sxBT) (pairTables sxAT⁻¹ sxBT⁻¹)
          (cosetOrderTables sxCert 1 5) [toTable sxAT] 40000 = true ∧
        repsTotal 24 (pairTables sxAT sxBT) (pairTables sxAT⁻¹ sxBT⁻¹) [toTable sxAT]
            (orderTables sxCert 4) 40000 (wordsTest 24 5 4 sxAutWords) = 138240) :=
  KernelAS91Sx.Sx664OC.facts

end Certificates
