module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
import Certificates.Kernel.SporSch.Mathieu.M24Facts
public meta import CFSG.Sporadic.Schreier.M24Base
public import CFSG.Sporadic.Schreier.M24Base
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu in
open CFSG.Sporadic.Schreier.Native in
theorem certificate2205 : (repsOK 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (cosetOrderTables m24Certificate 1 2) (m24InvReps.map toTable) 40000 = true ∧
      repSizes 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (m24InvReps.map toTable) 40000 = [31878, 11385] ∧
      (m24InvReps.map toTable).all (ordTest 24 2) = true
    )
    ∧ (m24CentQ1.check = true ∧ m24CentQ1.orderCertificate = 7680 ∧
      (m24CentWords1.map (evalCodes [m24gA, m24gB])).all
        (fun h => commT 24 (toTable h) (toTable ((m24InvReps).getD 0 1))) = true ∧
      oddWitnessOK 24 15 (allTables m24CentQ1) = true
    )
    ∧ (m24CentQ2.check = true ∧ m24CentQ2.orderCertificate = 21504 ∧
      (m24CentWords2.map (evalCodes [m24gA, m24gB])).all
        (fun h => commT 24 (toTable h) (toTable ((m24InvReps).getD 1 1))) = true ∧
      oddWitnessOK 24 21 (allTables m24CentQ2) = true
    )
    ∧ (ordTest 24 2 (toTable m24gA) = true ∧ ordTest 24 3 (toTable m24gB) = true ∧
      wordsTest 24 2 3 m24AutWords (toTable m24gA) (toTable m24gB) = true ∧
      repsTotal 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (m24InvReps.map toTable) (orderTables m24Certificate 3) 40000 (wordsTest 24 2 3 m24AutWords) =
          244823040
    ) := KernelSporSch.M24OC.facts2205

end Certificates
