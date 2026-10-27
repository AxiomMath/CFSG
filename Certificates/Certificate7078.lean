module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoCertInputs
import Certificates.Kernel.CosetW.Assembly

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.L34Amalgam MulAction CFSG.ComponentClassification.WittDesign in
open CFSG.Quasithin.Asc94 CFSG.CosetTable in
theorem certificate7078 :
    (subsetCheck relsP1 [] 100000 960 = true)
    ∧ (subsetCheck relsP2 [] 100000 960 = true) := CosetW.proof7078

end Certificates
