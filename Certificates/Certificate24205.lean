module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.AaData
import Certificates.Kernel.Th.Fam.C24205
import Certificates.Kernel.Th.Fam.Ctx

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.Th.Expr CertificateChecks.KernelTh.Fam.Local

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.EvenSporadicStandard.ThStd.LocalDataTh in
theorem certificate24205 : ∀ e < 15, ∀ c < 16, eqRows (rowsPE (e + 1)) (rowsAEl c) = false := by
  refine fun e he c hc => ?_
  have h := List.all_eq_true.1 (List.all_eq_true.1 KernelTh.Fam.ok24205 e (List.mem_range.2 he)) c
    (List.mem_range.2 hc)
  kernel_exact eqRows_false_of (e := peT (e + 1)) (f := aelT c) KernelTh.Fam.thCtx h

end Certificates
