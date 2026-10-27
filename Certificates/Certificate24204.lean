module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.AaData
import Certificates.Kernel.Th.Fam.C24204
import Certificates.Kernel.Th.Fam.Ctx

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.EvenSporadicStandard.ThStd.LocalDataTh in
theorem certificate24204 :
    eqRows (mulRows rowsG1 rowsG2) (mulRows rowsG2 rowsG1) = true ∧
    eqRows (mulRows rowsG1 rowsG3) (mulRows rowsG3 rowsG1) = true ∧
    eqRows (mulRows rowsG1 rowsG4) (mulRows rowsG4 rowsG1) = true ∧
    eqRows (mulRows rowsG2 rowsG3) (mulRows rowsG3 rowsG2) = true ∧
    eqRows (mulRows rowsG2 rowsG4) (mulRows rowsG4 rowsG2) = true ∧
    eqRows (mulRows rowsG3 rowsG4) (mulRows rowsG4 rowsG3) = true ∧
    eqRows (mulRows rowsG1 rowsG1) (rowsAEl 2) = true ∧
    eqRows (mulRows rowsG2 rowsG2) (rowsAEl 1) = true ∧
    eqRows (mulRows rowsG3 rowsG3) (rowsAEl 5) = true ∧
    eqRows (mulRows rowsG4 rowsG4) (rowsAEl 10) = true ∧
    eqRows (mulRows rowsG1 rowsZ) (mulRows rowsZ rowsG1) = true ∧
    eqRows (mulRows rowsG1 rowsA1) (mulRows rowsA1 rowsG1) = true ∧
    eqRows (mulRows rowsG1 rowsA2) (mulRows rowsA2 rowsG1) = true ∧
    eqRows (mulRows rowsG1 rowsA3) (mulRows rowsA3 rowsG1) = true ∧
    eqRows (mulRows rowsG2 rowsZ) (mulRows rowsZ rowsG2) = true ∧
    eqRows (mulRows rowsG2 rowsA1) (mulRows rowsA1 rowsG2) = true ∧
    eqRows (mulRows rowsG2 rowsA2) (mulRows rowsA2 rowsG2) = true ∧
    eqRows (mulRows rowsG2 rowsA3) (mulRows rowsA3 rowsG2) = true ∧
    eqRows (mulRows rowsG3 rowsZ) (mulRows rowsZ rowsG3) = true ∧
    eqRows (mulRows rowsG3 rowsA1) (mulRows rowsA1 rowsG3) = true ∧
    eqRows (mulRows rowsG3 rowsA2) (mulRows rowsA2 rowsG3) = true ∧
    eqRows (mulRows rowsG3 rowsA3) (mulRows rowsA3 rowsG3) = true ∧
    eqRows (mulRows rowsG4 rowsZ) (mulRows rowsZ rowsG4) = true ∧
    eqRows (mulRows rowsG4 rowsA1) (mulRows rowsA1 rowsG4) = true ∧
    eqRows (mulRows rowsG4 rowsA2) (mulRows rowsA2 rowsG4) = true ∧
    eqRows (mulRows rowsG4 rowsA3) (mulRows rowsA3 rowsG4) = true ∧
    eqRows (mulRows rowsBe rowsZ) (mulRows rowsZ rowsBe) = true ∧
    eqRows (mulRows rowsBe rowsA1) (mulRows rowsA1 rowsBe) = true ∧
    eqRows (mulRows rowsBe rowsA2) (mulRows rowsA2 rowsBe) = true ∧
    eqRows (mulRows rowsBe rowsA3) (mulRows rowsA3 rowsBe) = true ∧
    eqRows (mulRows rowsBe rowsBe) idRows = true ∧
    eqRows (mulRows (mulRows rowsBe rowsG1) rowsBe)
      (mulRows rowsG1 (mulRows rowsG1 rowsG1)) = true ∧
    eqRows (mulRows (mulRows rowsBe rowsG2) rowsBe)
      (mulRows rowsG2 (mulRows rowsG2 rowsG2)) = true ∧
    eqRows (mulRows (mulRows rowsBe rowsG3) rowsBe)
      (mulRows rowsG3 (mulRows rowsG3 rowsG3)) = true ∧
    eqRows (mulRows (mulRows rowsBe rowsG4) rowsBe)
      (mulRows rowsG4 (mulRows rowsG4 rowsG4)) = true := by
  kernel_exact CFSG.KC.Th.Expr.facts_of KernelTh.Fam.thCtx KernelTh.Fam.l24204 KernelTh.Fam.ok24204

end Certificates
