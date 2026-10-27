module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
import Certificates.Kernel.SporSch.Mathieu.M12MFacts
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreOuter

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu in
open CFSG.Sporadic.Schreier.Native in
theorem certificate2201 : (m12D.check = true ∧ m12D.orderCertificate = 95040)
    ∧ (m12Sigma * m12Sigma = 1 ∧ m12D.sift (m12Sigma * m12A1 * m12Sigma⁻¹) 0 = true ∧
      m12D.sift (m12Sigma * m12B1 * m12Sigma⁻¹) 0 = true ∧
      countProducts 24 (commAll 24 [toTable m12A1, toTable m12B1]) (levelTables m12D)
        (toTable m12Sigma) = 0
    )
    ∧ (repsOK 24 (pairTables m12A1 m12B1) (pairTables m12A1⁻¹ m12B1⁻¹)
        (cosetOrderTables m12D m12Sigma 2) ([m12Sigma].map toTable) 1000 = true ∧
      repSizes 24 (pairTables m12A1 m12B1) (pairTables m12A1⁻¹ m12B1⁻¹)
        ([m12Sigma].map toTable) 1000 = [792] ∧
      ordTest 24 2 (toTable m12Sigma) = true
    )
    ∧ (m12SigmaCentQ.check = true ∧ m12SigmaCentQ.orderCertificate = 120 ∧
      (m12SigmaCentWords.map (evalCodes [m12A1, m12B1])).all
        (fun h => commT 24 (toTable h) (toTable m12Sigma)) = true ∧
      oddWitnessOK 24 15 (allTables m12SigmaCentQ) = true
    ) := KernelSporSch.M12MOC.facts

end Certificates
