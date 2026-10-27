module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
public import Certificates.Certificate2201

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native

theorem m12D_check : m12D.check = true ∧ m12D.orderCertificate = 95040 :=
  Certificates.certificate2201.1

theorem m12_sigma_check :
    m12Sigma * m12Sigma = 1 ∧ m12D.sift (m12Sigma * m12A1 * m12Sigma⁻¹) 0 = true ∧
    m12D.sift (m12Sigma * m12B1 * m12Sigma⁻¹) 0 = true ∧
    countProducts 24 (commAll 24 [toTable m12A1, toTable m12B1]) (levelTables m12D)
      (toTable m12Sigma) = 0 :=
  Certificates.certificate2201.2.1

theorem m12_sigma_cover :
    repsOK 24 (pairTables m12A1 m12B1) (pairTables m12A1⁻¹ m12B1⁻¹)
      (cosetOrderTables m12D m12Sigma 2) ([m12Sigma].map toTable) 1000 = true ∧
    repSizes 24 (pairTables m12A1 m12B1) (pairTables m12A1⁻¹ m12B1⁻¹)
      ([m12Sigma].map toTable) 1000 = [792] ∧
    ordTest 24 2 (toTable m12Sigma) = true :=
  Certificates.certificate2201.2.2.1

theorem m12_sigma_cent :
    m12SigmaCentQ.check = true ∧ m12SigmaCentQ.orderCertificate = 120 ∧
    (m12SigmaCentWords.map (evalCodes [m12A1, m12B1])).all
      (fun h => commT 24 (toTable h) (toTable m12Sigma)) = true ∧
    oddWitnessOK 24 15 (allTables m12SigmaCentQ) = true :=
  Certificates.certificate2201.2.2.2

end CFSG.Sporadic.Schreier
