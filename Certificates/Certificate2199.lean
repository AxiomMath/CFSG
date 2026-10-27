module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM11Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM11Data
import Certificates.Kernel.SporSch.Mathieu.M11Facts
public meta import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu in
open CFSG.Sporadic.Schreier.Native in
theorem certificate2199 : (repsOK 11 (pairTables m11gA m11gB) (pairTables m11gA⁻¹ m11gB⁻¹)
        (cosetOrderTables m11Certificate 1 2) (m11InvReps.map toTable) 400 = true ∧
      repSizes 11 (pairTables m11gA m11gB) (pairTables m11gA⁻¹ m11gB⁻¹)
        (m11InvReps.map toTable) 400 = [165] ∧
      (m11InvReps.map toTable).all (ordTest 11 2) = true
    )
    ∧ (m11CentQ1.check = true ∧ m11CentQ1.orderCertificate = 48 ∧
      (m11CentWords1.map (evalCodes [m11gA, m11gB])).all
        (fun h => commT 11 (toTable h) (toTable ((m11InvReps).getD 0 1))) = true ∧
      oddWitnessOK 11 3 (allTables m11CentQ1) = true
    )
    ∧ (ordTest 11 2 (toTable m11gA) = true ∧ ordTest 11 4 (toTable m11gB) = true ∧
      wordsTest 11 2 4 m11AutWords (toTable m11gA) (toTable m11gB) = true ∧
      repsTotal 11 (pairTables m11gA m11gB) (pairTables m11gA⁻¹ m11gB⁻¹)
        (m11InvReps.map toTable) (orderTables m11Certificate 4) 400 (wordsTest 11 2 4 m11AutWords) =
          7920
    ) := KernelSporSch.M11OC.facts

end Certificates
