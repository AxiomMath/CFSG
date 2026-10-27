module

public import CFSG.Sporadic.Presentation.Fi24PrimeExactInputs
import Certificates.Kernel.Fi24.Bridge
import Certificates.Kernel.Fi24PG10.Bridge
public import CFSG.Sporadic.Presentation.Common

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Presentation CFSG.Sporadic.Presentation.Fi24Prime in
open CFSG.CosetTable in
theorem certificate9113 : (Finite TauCeti.SporadicName.Fi24Prime.Group ∧
      Nat.card TauCeti.SporadicName.Fi24Prime.Group ≤ 1255205709190661721292800) ∧
    (Finite (PG (subsetOf _ [0, 1, 2, 3, 4, 5, 6, 7, 9, 10]).length X1) ∧
      Nat.card (PG (subsetOf _ [0, 1, 2, 3, 4, 5, 6, 7, 9, 10]).length X1) ≤ 4089470473293004800) := ⟨KernelFi24.fi24Prime, KernelPG10.pg10_card⟩

end Certificates
