module

public import Certificates.Data.GMS78RuNModel
import Certificates.Kernel.GMS78.NM

public section

namespace Certificates

open CertificateChecks

theorem certificate15109 : CFSG.GMS78RuN.nQuadCheck = true ∧ CFSG.GMS78RuN.nCompCheck = true ∧
    CFSG.GMS78RuN.nIdCheck = true ∧ CFSG.GMS78RuN.nFaithCheck = true ∧
    CFSG.GMS78RuN.nImgCheck = true ∧ CFSG.GMS78RuN.nRelCheck = true ∧
    CFSG.GMS78RuN.nCloCheck = true ∧ CFSG.GMS78RuN.nA0Check = true := KernelGMS78.nModel_eq

end Certificates
