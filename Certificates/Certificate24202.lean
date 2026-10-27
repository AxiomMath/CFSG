module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.NormData
import Certificates.Kernel.Th.Fam.C24202
import Certificates.Kernel.Th.Fam.Ctx

public section

namespace Certificates

open CertificateChecks

set_option maxRecDepth 100000 in
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.EvenSporadicStandard.ThStd.LocalDataTh in
theorem certificate24202 :
    eqRows (mulRows rowsN1 rowsZ) (mulRows (rowsAEl 1) rowsN1) = true ∧
    eqRows (mulRows rowsN1 rowsA1) (mulRows (rowsAEl 2) rowsN1) = true ∧
    eqRows (mulRows rowsN1 rowsA2) (mulRows (rowsAEl 10) rowsN1) = true ∧
    eqRows (mulRows rowsN1 rowsA3) (mulRows (rowsAEl 15) rowsN1) = true ∧
    eqRows (mulRows rowsN2 rowsZ) (mulRows (rowsAEl 9) rowsN2) = true ∧
    eqRows (mulRows rowsN2 rowsA1) (mulRows (rowsAEl 1) rowsN2) = true ∧
    eqRows (mulRows rowsN2 rowsA2) (mulRows (rowsAEl 5) rowsN2) = true ∧
    eqRows (mulRows rowsN2 rowsA3) (mulRows (rowsAEl 2) rowsN2) = true := by
  kernel_exact CFSG.KC.Th.Expr.facts_of KernelTh.Fam.thCtx KernelTh.Fam.l24202 KernelTh.Fam.ok24202

end Certificates
