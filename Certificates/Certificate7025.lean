module

import Certificates.Kernel.CosetW.Assembly
public import CFSG.Quasithin.Recognition.L34AmalgamDataBase

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.L34Amalgam CFSG.CosetTable in
theorem certificate7025 :
    (∀ i : Fin 12, ∀ k ∈ [2, 3], ¬ (IsGood i ∧ k = 3) →
       subsetCheck (relsOf i k) [0, 1, 2, 3] 100000 1 = true)
    ∧ (∀ i : Fin 12, IsGood i →
       subsetCheck (relsOf i 3) [0, 1, 2, 3] 100000 21 = true)
    ∧ (∀ i : Fin 12, IsGood i →
       subsetCheck (restrictWords (subsetOf 5 [0, 1, 2, 3]) (relsOf i 3)) [] 100000 960 = true) := CosetW.proof7025

end Certificates
