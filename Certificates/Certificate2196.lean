
module


public import CFSG.Sporadic.Schreier.M23Data
import Certificates.Kernel.SporSch.Mathieu.M23Facts
public import CFSG.Sporadic.Schreier.ClassSum

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Schreier.Native in
theorem certificate2196 : (m23Certificate.check = true)
    ∧ (ordTest 23 2 (toTable m23PermA) = true ∧ ordTest 23 4 (toTable m23PermB) = true ∧
      pairTest 23 23 6 2 4 (toTable m23PermA) (toTable m23PermB) = true
    )
    ∧ ((orderTables m23Certificate 2).length = 3795 ∧
      (orderTables m23Certificate 4).length = 318780 ∧
      CFSG.Sporadic.Schreier.Native.classOK 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (orderTables m23Certificate 2) 4000 = true ∧
      classTotal 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (orderTables m23Certificate 2) (orderTables m23Certificate 4) 4000 23 6 2 4 =
        20401920
    ) := KernelSporSch.M23OC.facts2196

end Certificates
