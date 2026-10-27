module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.TransvData
import Certificates.Kernel.Th.Fam.C24216
import Certificates.Kernel.Th.Fam.Ctx

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.EvenSporadicStandard.ThStd.LocalDataTh in
theorem certificate24216 :
    eqRows (mulRows (rowsQ 1) rowsZ) (mulRows (rowsAEl 1) (rowsQ 1)) = true ∧
    eqRows (mulRows (rowsQ 1) rowsA1) (mulRows (rowsAEl 3) (rowsQ 1)) = true ∧
    eqRows (mulRows (rowsQ 1) rowsA2) (mulRows (rowsAEl 4) (rowsQ 1)) = true ∧
    eqRows (mulRows (rowsQ 1) rowsA3) (mulRows (rowsAEl 8) (rowsQ 1)) = true ∧
    eqRows (mulRows (rowsQ 1) rowsG1) (mulRows (rowsGE 1 1 2 2) (rowsQ 1)) = true ∧
    eqRows (mulRows (rowsQ 1) rowsG2) (mulRows (rowsGE 0 1 0 0) (rowsQ 1)) = true ∧
    eqRows (mulRows (rowsQ 1) rowsG3) (mulRows (rowsGE 2 0 3 2) (rowsQ 1)) = true ∧
    eqRows (mulRows (rowsQ 1) rowsG4) (mulRows (rowsGE 0 3 0 3) (rowsQ 1)) = true := by
  kernel_exact CFSG.KC.Th.Expr.facts_of KernelTh.Fam.thCtx KernelTh.Fam.l24216 KernelTh.Fam.ok24216

end Certificates
