module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
public import Certificates.Certificate2205

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native

theorem m24_oddcore_cover :
    repsOK 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
      (cosetOrderTables m24Certificate 1 2) (m24InvReps.map toTable) 40000 = true ∧
    repSizes 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
      (m24InvReps.map toTable) 40000 = [31878, 11385] ∧
    (m24InvReps.map toTable).all (ordTest 24 2) = true :=
  Certificates.certificate2205.1

theorem m24_oddcore_cent1 :
    m24CentQ1.check = true ∧ m24CentQ1.orderCertificate = 7680 ∧
    (m24CentWords1.map (evalCodes [m24gA, m24gB])).all
      (fun h => commT 24 (toTable h) (toTable ((m24InvReps).getD 0 1))) = true ∧
    oddWitnessOK 24 15 (allTables m24CentQ1) = true :=
  Certificates.certificate2205.2.1

theorem m24_oddcore_cent2 :
    m24CentQ2.check = true ∧ m24CentQ2.orderCertificate = 21504 ∧
    (m24CentWords2.map (evalCodes [m24gA, m24gB])).all
      (fun h => commT 24 (toTable h) (toTable ((m24InvReps).getD 1 1))) = true ∧
    oddWitnessOK 24 21 (allTables m24CentQ2) = true :=
  Certificates.certificate2205.2.2.1

theorem m24_oddcore_aut :
    ordTest 24 2 (toTable m24gA) = true ∧ ordTest 24 3 (toTable m24gB) = true ∧
    wordsTest 24 2 3 m24AutWords (toTable m24gA) (toTable m24gB) = true ∧
    repsTotal 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
      (m24InvReps.map toTable) (orderTables m24Certificate 3) 40000 (wordsTest 24 2 3 m24AutWords) =
        244823040 :=
  Certificates.certificate2205.2.2.2

end CFSG.Sporadic.Schreier
