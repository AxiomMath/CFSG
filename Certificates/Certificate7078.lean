module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoCertInputs
import Certificates.Kernel.CosetW.Assembly

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.L34Amalgam MulAction CFSG.ComponentClassification.WittDesign in
open CFSG.Quasithin.Asc94 CFSG.CosetTable in
theorem certificate7078 :
    (subsetCheck relsP1 [0, 2] 100000 80 = true ∧
      subsetCheck (restrictWords (subsetOf 5 [0, 2]) relsP1) [] 100000 12 = true)
    ∧ (subsetCheck relsP2 [0, 2] 100000 80 = true ∧
      subsetCheck (restrictWords (subsetOf 5 [0, 2]) relsP2) [] 100000 12 = true) :=
  CosetW.proof7078

end Certificates
