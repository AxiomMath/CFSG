module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM12Data
import Certificates.Kernel.SporSch.Mathieu.M12Facts
public import CFSG.Sporadic.Schreier.M12
public meta import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu in
open CFSG.Sporadic.Schreier.Native in
theorem certificate2200 : (repsOK 12 (pairTables m12gA m12gB) (pairTables m12gA⁻¹ m12gB⁻¹)
        (cosetOrderTables m12Certificate 1 2) (m12InvReps.map toTable) 1000 = true ∧
      repSizes 12 (pairTables m12gA m12gB) (pairTables m12gA⁻¹ m12gB⁻¹)
        (m12InvReps.map toTable) 1000 = [495, 396] ∧
      (m12InvReps.map toTable).all (ordTest 12 2) = true
    )
    ∧ (m12CentQ1.check = true ∧ m12CentQ1.orderCertificate = 192 ∧
      (m12CentWords1.map (evalCodes [m12gA, m12gB])).all
        (fun h => commT 12 (toTable h) (toTable ((m12InvReps).getD 0 1))) = true ∧
      oddWitnessOK 12 3 (allTables m12CentQ1) = true
    )
    ∧ (m12CentQ2.check = true ∧ m12CentQ2.orderCertificate = 240 ∧
      (m12CentWords2.map (evalCodes [m12gA, m12gB])).all
        (fun h => commT 12 (toTable h) (toTable ((m12InvReps).getD 1 1))) = true ∧
      oddWitnessOK 12 15 (allTables m12CentQ2) = true
    )
    ∧ (ordTest 12 2 (toTable m12gA) = true ∧ ordTest 12 3 (toTable m12gB) = true ∧
      wordsTest 12 2 3 m12AutWords (toTable m12gA) (toTable m12gB) = true ∧
      repsTotal 12 (pairTables m12gA m12gB) (pairTables m12gA⁻¹ m12gB⁻¹)
        (m12InvReps.map toTable) (orderTables m12Certificate 3) 1000 (wordsTest 12 2 3 m12AutWords) =
          190080
    ) := KernelSporSch.M12OC.facts

end Certificates
