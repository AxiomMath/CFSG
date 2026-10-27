module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM12Data
public import Certificates.Certificate2200

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native

theorem m12_oddcore_cover :
    repsOK 12 (pairTables m12gA m12gB) (pairTables m12gA⁻¹ m12gB⁻¹)
      (cosetOrderTables m12Certificate 1 2) (m12InvReps.map toTable) 1000 = true ∧
    repSizes 12 (pairTables m12gA m12gB) (pairTables m12gA⁻¹ m12gB⁻¹)
      (m12InvReps.map toTable) 1000 = [495, 396] ∧
    (m12InvReps.map toTable).all (ordTest 12 2) = true :=
  Certificates.certificate2200.1

theorem m12_oddcore_cent1 :
    m12CentQ1.check = true ∧ m12CentQ1.orderCertificate = 192 ∧
    (m12CentWords1.map (evalCodes [m12gA, m12gB])).all
      (fun h => commT 12 (toTable h) (toTable ((m12InvReps).getD 0 1))) = true ∧
    oddWitnessOK 12 3 (allTables m12CentQ1) = true :=
  Certificates.certificate2200.2.1

theorem m12_oddcore_cent2 :
    m12CentQ2.check = true ∧ m12CentQ2.orderCertificate = 240 ∧
    (m12CentWords2.map (evalCodes [m12gA, m12gB])).all
      (fun h => commT 12 (toTable h) (toTable ((m12InvReps).getD 1 1))) = true ∧
    oddWitnessOK 12 15 (allTables m12CentQ2) = true :=
  Certificates.certificate2200.2.2.1

theorem m12_oddcore_aut :
    ordTest 12 2 (toTable m12gA) = true ∧ ordTest 12 3 (toTable m12gB) = true ∧
    wordsTest 12 2 3 m12AutWords (toTable m12gA) (toTable m12gB) = true ∧
    repsTotal 12 (pairTables m12gA m12gB) (pairTables m12gA⁻¹ m12gB⁻¹)
      (m12InvReps.map toTable) (orderTables m12Certificate 3) 1000 (wordsTest 12 2 3 m12AutWords) =
        190080 :=
  Certificates.certificate2200.2.2.2

end CFSG.Sporadic.Schreier
