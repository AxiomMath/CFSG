module

public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JConditionInputs
import Certificates.Kernel.LocalComp.Sp6J.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.Sp6 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
    CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.M12Cover
    CFSG.Sporadic.Schreier in
theorem certificate3088 : (sp6Q.check = true ∧ sp6Q.orderCertificate = 1451520 ∧
       siftA 36 (rawLevels 36 co3Sp36Arrs co3Sp36BaseArr) co3Sp36BaseArr 0
         (Array.ofFn fun i => (sp6A i : ℕ)) = true ∧
       siftA 36 (rawLevels 36 co3Sp36Arrs co3Sp36BaseArr) co3Sp36BaseArr 0
         (Array.ofFn fun i => (sp6B i : ℕ)) = true)
    ∧ (repsOK 36 (listTables sp6Gens) (listTables (sp6Gens.map (·⁻¹)))
         (cosetOrderTables sp6Q 1 2) (sp6InvReps.map toTable) 4000 = true ∧
       repSizes 36 (listTables sp6Gens) (listTables (sp6Gens.map (·⁻¹)))
         (sp6InvReps.map toTable) 4000 = [63, 315, 945, 3780] ∧
       (sp6InvReps.map toTable).all (ordTest 36 2) = true)
    ∧ (centCheck sp6CentQ1 23040 sp6CentGens1 sp6FourReps1 sp6Rep1 = true)
    ∧ (centCheck sp6CentQ2 4608 sp6CentGens2 sp6FourReps2 sp6Rep2 = true)
    ∧ (centCheck sp6CentQ3 1536 sp6CentGens3 sp6FourReps3 sp6Rep3 = true)
    ∧ (centCheck sp6CentQ4 384 sp6CentGens4 sp6FourReps4 sp6Rep4 = true) := KernelLC.Sp6J.facts

end Certificates
