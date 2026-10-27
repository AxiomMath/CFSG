module

public import CFSG.Sporadic.Recognition.Co2MultiplierInputs
import Certificates.Kernel.Co2Mult.Tab
import Certificates.Kernel.Co2Mult.Bound

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.Co2Multiplier in
theorem certificate24011 : (co2TabCheck = true) ∧
    ((genSub (wordSet co2Cover) (subsetOf 7 [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
      (genSub (wordSet co2Cover) (subsetOf 7 [0, 1, 2, 3, 4, 5])).index ≤ 47104) :=
  ⟨KernelCo2Mult.tab, KernelCo2Mult.cover_index⟩

end Certificates
