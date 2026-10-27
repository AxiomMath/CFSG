module

public import CFSG.Sporadic.Schreier.MathieuSylowAutM23Inputs
public import CFSG.Sporadic.Schreier.MathieuSylowAutM23Derivs
public import CFSG.Sporadic.Schreier.MathieuSylowAutCent
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M23
public meta import CFSG.Sporadic.Schreier.M23Pinned
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
import Certificates.Kernel.Sporadic.M23Syl.Facts
import Certificates.Kernel.Sporadic.M23Syl.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.Certificates in
open CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Schreier.Native in
theorem certificate2209 : (sylowAutOK 23 (toTable m23PermA) (toTable m23PermB) m23Derivs
      m23SylowExprs (natTbl 23 m23SylowZ) 150 10200960 7 = true
    )
    ∧ (sylCentOK 23 (sylowGens 23 (toTable m23PermA) (toTable m23PermB) m23Derivs m23SylowExprs)
      (natTbl 23 m23SylowZ) (toTable m23PermB) (allTables m23CentQ1) = true
    )
    ∧ ((repsOK 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
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
    )) := KernelSpor.M23Syl.facts

end Certificates
