module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoCertInputs
import Certificates.Kernel.L34Pk.A7079

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.L34Amalgam MulAction CFSG.ComponentClassification.WittDesign in
open CFSG.Quasithin.Asc94 CFSG.CosetTable in
theorem certificate7079 :
    (a2Check genTL genTiL = true)
    ∧ (pqCheck genTL genTiL crdTL = true)
    ∧ (invCheck genTL genTiL crdTL = true)
    ∧ (conjCheck genTL genTiL = true)
    ∧ (s1Check genTL genTiL = true)
    ∧ (rhCheck genTL genTiL = true)
    ∧ (glueCheck genTL genTiL crdTL = true) := KernelL34.facts7079

end Certificates
