
module


public import Certificates.Data.CFSGNative.Co1.S365CentPath
public import CFSG.Monster.GMS.S365CosetInputs
import Certificates.Kernel.Co1M.C10042

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.S365Native CFSG.Sporadic.Co1.S365CentNative in
theorem certificate10042 :
    (cosetRowsT.all fun Mt => isFixedN Mt 2 && isFixedN Mt 4) = true ∧
    pat4 qRows (CFSG.Sporadic.Co1.Module.orbitOf 2 98280).pts (posTable 24 (CFSG.Sporadic.Co1.Module.orbitOf 2 98280).pts) 98280 2 4 cosetBase =
      true ∧
    countBelow (pat4 qRows (CFSG.Sporadic.Co1.Module.orbitOf 2 98280).pts (posTable 24 (CFSG.Sporadic.Co1.Module.orbitOf 2 98280).pts) 98280 2 4)
      16777216 0 = 1995840 ∧
    ∃ R : Finset ℕ, R.card = 498960 ∧ ∀ r ∈ R, r < 2 ^ 24 ∧ ∃ w : List ℕ, (∀ l ∈ w, l < 3) ∧
      canon4 2 4 (applyPath cosetRowsT w cosetBase) = r := KernelCo1M.c10042

end Certificates
