module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
import Certificates.Kernel.SporSch.Mathieu.M23Facts
public import CFSG.Sporadic.M23.M23Group
public meta import CFSG.Sporadic.M23.M23Group
public meta import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Schreier.M23Base
public meta import CFSG.Sporadic.Schreier.M23Base
public import CFSG.Sporadic.Schreier.M23CheckBase
public meta import CFSG.Sporadic.Schreier.M23CheckBase
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.Outer
public meta import CFSG.Sporadic.Schreier.Outer

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu in
open CFSG.Sporadic.Schreier.Native in
theorem certificate2204 : (repsOK 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (cosetOrderTables m23Certificate 1 2) (m23InvReps.map toTable) 4000 = true ∧
      repSizes 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (m23InvReps.map toTable) 4000 = [3795] ∧
      (m23InvReps.map toTable).all (ordTest 23 2) = true
    )
    ∧ (m23CentQ1.check = true ∧ m23CentQ1.orderCertificate = 2688 ∧
      (m23CentWords1.map (evalCodes [m23PermA, m23PermB])).all
        (fun h => commT 23 (toTable h) (toTable ((m23InvReps).getD 0 1))) = true ∧
      oddWitnessOK 23 21 (allTables m23CentQ1) = true
    )
    ∧ (ordTest 23 2 (toTable m23PermA) = true ∧ ordTest 23 4 (toTable m23PermB) = true ∧
      wordsTest 23 2 4 m23AutWords (toTable m23PermA) (toTable m23PermB) = true ∧
      repsTotal 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
        (m23InvReps.map toTable) (orderTables m23Certificate 4) 4000 (wordsTest 23 2 4 m23AutWords) =
          10200960
    ) := KernelSporSch.M23OC.facts2204

end Certificates
