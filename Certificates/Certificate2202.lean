module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22Data
import Certificates.Kernel.SporSch.Mathieu.M22Facts
public meta import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu in
open CFSG.Sporadic.Schreier.Native in
theorem certificate2202 : (repsOK 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
        (cosetOrderTables m22Certificate 1 2) (m22InvReps.map toTable) 2000 = true ∧
      repSizes 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
        (m22InvReps.map toTable) 2000 = [1155] ∧
      (m22InvReps.map toTable).all (ordTest 22 2) = true
    )
    ∧ (m22CentQ1.check = true ∧ m22CentQ1.orderCertificate = 384 ∧
      (m22CentWords1.map (evalCodes [m22gA, m22gB])).all
        (fun h => commT 22 (toTable h) (toTable ((m22InvReps).getD 0 1))) = true ∧
      oddWitnessOK 22 3 (allTables m22CentQ1) = true
    )
    ∧ (ordTest 22 2 (toTable m22gA) = true ∧ ordTest 22 4 (toTable m22gB) = true ∧
      wordsTest 22 2 4 m22AutWords (toTable m22gA) (toTable m22gB) = true ∧
      repsTotal 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
        (m22InvReps.map toTable) (orderTables m22Certificate 4) 2000 (wordsTest 22 2 4 m22AutWords) =
          887040
    ) := KernelSporSch.M22OC.facts

end Certificates
