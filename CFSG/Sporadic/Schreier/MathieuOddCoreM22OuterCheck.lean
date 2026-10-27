module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
public import Certificates.Certificate2203

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native

theorem m22_outer_delta :
    m22Delta * m22Delta = 1 ∧ m22Certificate.sift (m22Delta * m22gA * m22Delta⁻¹) 0 = true ∧
    m22Certificate.sift (m22Delta * m22gB * m22Delta⁻¹) 0 = true ∧
    countProducts 22 (commAll 22 [toTable m22gA, toTable m22gB]) (levelTables m22Certificate)
      (toTable m22Delta) = 0 :=
  Certificates.certificate2203.1

theorem m22_outer_cover :
    repsOK 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
      (cosetOrderTables m22Certificate m22Delta 2) (m22OutReps.map toTable) 2000 = true ∧
    repSizes 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
      (m22OutReps.map toTable) 2000 = [1386, 330] ∧
    (m22OutReps.map toTable).all (ordTest 22 2) = true :=
  Certificates.certificate2203.2.1

theorem m22_outer_cent1 :
    m22OutCentQ1.check = true ∧ m22OutCentQ1.orderCertificate = 320 ∧
    (m22OutCentWords1.map (evalCodes [m22gA, m22gB])).all
      (fun h => commT 22 (toTable h) (toTable (m22OutReps.getD 0 1))) = true ∧
    oddWitnessOK 22 5 (allTables m22OutCentQ1) = true :=
  Certificates.certificate2203.2.2.1

theorem m22_outer_cent2 :
    m22OutCentQ2.check = true ∧ m22OutCentQ2.orderCertificate = 1344 ∧
    (m22OutCentWords2.map (evalCodes [m22gA, m22gB])).all
      (fun h => commT 22 (toTable h) (toTable (m22OutReps.getD 1 1))) = true ∧
    oddWitnessOK 22 21 (allTables m22OutCentQ2) = true :=
  Certificates.certificate2203.2.2.2

end CFSG.Sporadic.Schreier
