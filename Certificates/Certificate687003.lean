module

public import Certificates.Data.Th687.MFactsA
import Certificates.Kernel.Th.Fam.C687003
import Certificates.Kernel.Th.Fam.Ctx

public section

namespace Certificates

open CFSG.KC.Th.Expr CertificateChecks.KernelTh.Fam

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 in
open CFSG.Sporadic.Th.Recog.MFactsData in
theorem certificate687003 :
    eqRows (mulRows (sqrtRowsGInv ()) (sqrtRowsG ())) idRows = true ∧
      eqRows (mulRows (sqrtRowsM ()) (sqrtRowsM ())) rowsZ = true ∧
      eqRows (mulRows (sqrtRowsM ()) (rowsQ 0)) (mulRows (rowsQ 0) (sqrtRowsM ())) = true ∧
      centPairCard () = 2 ^ 8 ∧
      invPairCard () = 143 ∧
      invQCard () = 270 ∧
      eqRows (rowsQ 0) idRows = false ∧
      eqRows (rowsQ 0) rowsZ = false := by
  obtain ⟨f1, f2, f3, f4, f5⟩ : TE.Facts l687003 := facts_of thCtx l687003 ok687003
  refine ⟨?_, ?_, ?_, cent_card, inv_card, invQ_card, ?_, ?_⟩
  · kernel_exact f1
  · kernel_exact f2
  · kernel_exact f3
  · kernel_exact f4
  · kernel_exact f5

end Certificates
