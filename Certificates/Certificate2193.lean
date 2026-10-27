module

public import CFSG.Sporadic.Schreier.M12Data
public meta import CFSG.Sporadic.Schreier.M12Data
import Certificates.Kernel.Sporadic.M12CountBridge
import Certificates.Kernel.Sporadic.M12CountNeg
public meta import CFSG.Sporadic.Schreier.ImagePairs
public import CFSG.Sporadic.Schreier.ImagePairs

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu in
open CFSG.Sporadic.Schreier.Native in
theorem certificate2193 : (m12Certificate.check = true)
    ∧ (ordTest 12 2 (toTable m12gA) = true ∧ ordTest 12 3 (toTable m12gB) = true ∧
      pairTest 12 11 6 2 3 (toTable m12gA) (toTable m12gB) = true
    )
    ∧ ((orderTables m12Certificate 2).length = 891 ∧
      (orderTables m12Certificate 3).length = 4400
    )
    ∧ (pairCount (orderTables m12Certificate 2) (orderTables m12Certificate 3)
      (pairTest 12 11 6 2 3) = 380160
    ) := KernelSpor.M12Count.counts

end Certificates
