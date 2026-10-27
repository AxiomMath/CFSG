module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public import Certificates.Certificate2204

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native

theorem m23_oddcore_cover :
    repsOK 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
      (cosetOrderTables m23Certificate 1 2) (m23InvReps.map toTable) 4000 = true ∧
    repSizes 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
      (m23InvReps.map toTable) 4000 = [3795] ∧
    (m23InvReps.map toTable).all (ordTest 23 2) = true :=
  Certificates.certificate2204.1

theorem m23_oddcore_cent1 :
    m23CentQ1.check = true ∧ m23CentQ1.orderCertificate = 2688 ∧
    (m23CentWords1.map (evalCodes [m23PermA, m23PermB])).all
      (fun h => commT 23 (toTable h) (toTable ((m23InvReps).getD 0 1))) = true ∧
    oddWitnessOK 23 21 (allTables m23CentQ1) = true :=
  Certificates.certificate2204.2.1

theorem m23_oddcore_aut :
    ordTest 23 2 (toTable m23PermA) = true ∧ ordTest 23 4 (toTable m23PermB) = true ∧
    wordsTest 23 2 4 m23AutWords (toTable m23PermA) (toTable m23PermB) = true ∧
    repsTotal 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
      (m23InvReps.map toTable) (orderTables m23Certificate 4) 4000 (wordsTest 23 2 4 m23AutWords) =
        10200960 :=
  Certificates.certificate2204.2.2

end CFSG.Sporadic.Schreier
