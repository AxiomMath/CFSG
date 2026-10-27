module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22Data
public import Certificates.Certificate2202

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native

theorem m22_oddcore_cover :
    repsOK 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
      (cosetOrderTables m22Certificate 1 2) (m22InvReps.map toTable) 2000 = true ∧
    repSizes 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
      (m22InvReps.map toTable) 2000 = [1155] ∧
    (m22InvReps.map toTable).all (ordTest 22 2) = true :=
  Certificates.certificate2202.1

theorem m22_oddcore_cent1 :
    m22CentQ1.check = true ∧ m22CentQ1.orderCertificate = 384 ∧
    (m22CentWords1.map (evalCodes [m22gA, m22gB])).all
      (fun h => commT 22 (toTable h) (toTable ((m22InvReps).getD 0 1))) = true ∧
    oddWitnessOK 22 3 (allTables m22CentQ1) = true :=
  Certificates.certificate2202.2.1

theorem m22_oddcore_aut :
    ordTest 22 2 (toTable m22gA) = true ∧ ordTest 22 4 (toTable m22gB) = true ∧
    wordsTest 22 2 4 m22AutWords (toTable m22gA) (toTable m22gB) = true ∧
    repsTotal 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
      (m22InvReps.map toTable) (orderTables m22Certificate 4) 2000 (wordsTest 22 2 4 m22AutWords) =
        887040 :=
  Certificates.certificate2202.2.2

end CFSG.Sporadic.Schreier
