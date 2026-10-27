module

public import CFSG.Sporadic.Schreier.MathieuSylowAutM24Inputs
public import CFSG.Sporadic.Schreier.MathieuSylowAutM24Derivs
public import CFSG.Sporadic.Schreier.MathieuSylowAutCent
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M24
public meta import CFSG.Monster.B.Mathieu.M24Check
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
import Certificates.Kernel.Sporadic.M24Syl.Facts
import Certificates.Kernel.Sporadic.M24Syl.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.Certificates in
open CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Schreier.Native in
theorem certificate2210 : (sylowAutOK 24 (toTable m24gA) (toTable m24gB) m24Derivs
      m24SylowExprs (natTbl 24 m24SylowZ) 1100 244823040 10 = true
    )
    ∧ (sylCentOK 24 (sylowGens 24 (toTable m24gA) (toTable m24gB) m24Derivs m24SylowExprs)
      (natTbl 24 m24SylowZ) (toTable m24gB) (allTables m24CentQ1) = true
    )
    ∧ ((repsOK 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
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
    )) := KernelSpor.M24Syl.facts

end Certificates
