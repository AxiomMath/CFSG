module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM11Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM11Data
public import Certificates.Certificate2199

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native

theorem m11_oddcore_cover :
    repsOK 11 (pairTables m11gA m11gB) (pairTables m11gA⁻¹ m11gB⁻¹)
      (cosetOrderTables m11Certificate 1 2) (m11InvReps.map toTable) 400 = true ∧
    repSizes 11 (pairTables m11gA m11gB) (pairTables m11gA⁻¹ m11gB⁻¹)
      (m11InvReps.map toTable) 400 = [165] ∧
    (m11InvReps.map toTable).all (ordTest 11 2) = true :=
  Certificates.certificate2199.1

theorem m11_oddcore_cent1 :
    m11CentQ1.check = true ∧ m11CentQ1.orderCertificate = 48 ∧
    (m11CentWords1.map (evalCodes [m11gA, m11gB])).all
      (fun h => commT 11 (toTable h) (toTable ((m11InvReps).getD 0 1))) = true ∧
    oddWitnessOK 11 3 (allTables m11CentQ1) = true :=
  Certificates.certificate2199.2.1

theorem m11_oddcore_aut :
    ordTest 11 2 (toTable m11gA) = true ∧ ordTest 11 4 (toTable m11gB) = true ∧
    wordsTest 11 2 4 m11AutWords (toTable m11gA) (toTable m11gB) = true ∧
    repsTotal 11 (pairTables m11gA m11gB) (pairTables m11gA⁻¹ m11gB⁻¹)
      (m11InvReps.map toTable) (orderTables m11Certificate 4) 400 (wordsTest 11 2 4 m11AutWords) =
        7920 :=
  Certificates.certificate2199.2.2

end CFSG.Sporadic.Schreier
