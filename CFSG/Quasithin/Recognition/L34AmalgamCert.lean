module

public import CFSG.Quasithin.Recognition.L34AmalgamData
public meta import CFSG.Quasithin.Recognition.L34AmalgamData
public meta import CFSG.Certificates.CosetTablePresented
public import Certificates.Certificate7025

public section

namespace CFSG.Quasithin.L34Amalgam

open CFSG.CosetTable

theorem cert_bad : ∀ i : Fin 12, ∀ k ∈ [2, 3], ¬ (IsGood i ∧ k = 3) →
    subsetCheck (relsOf i k) [0, 1, 2, 3] 100000 1 = true :=
  Certificates.certificate7025.1

theorem cert_good : ∀ i : Fin 12, IsGood i →
    subsetCheck (relsOf i 3) [0, 1, 2, 3] 100000 21 = true :=
  Certificates.certificate7025.2.1

theorem cert_P1 : ∀ i : Fin 12, IsGood i →
    subsetCheck (restrictWords (subsetOf 5 [0, 1, 2, 3]) (relsOf i 3)) [] 100000 960 = true :=
  Certificates.certificate7025.2.2

end CFSG.Quasithin.L34Amalgam
