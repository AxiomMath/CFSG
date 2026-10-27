module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.Milestones.ASVolI.F48.Small.U42eInputs
import Certificates.Kernel.PresLetters.F7552
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Data.Kernel.Bounds.TableFact

public section

open CFSG CFSG.ASVolI CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates

namespace CertificateChecks.PresLetters7552

#kc_forall_chunks idx (fun k => KB.TableFact 5 ((burnsideF48s_u42eWs k).map encW)
  ((subsetOf 5 [0, 1, 2, 4]).map fun x => [(x.val, true)])
  (if k ∈ [0, 5, 8, 11, 17, 22, 27, 67, 73, 77, 83] then 45 else 1)) 98 CFSG.KBFact.F7552a 1

#kc_forall_chunks res (fun k => KB.TableFact (subsetOf 5 [0, 1, 2, 4]).length
  ((burnsideF48s_u42eWsB k).map encW) [] 1152) 98 CFSG.KBFact.F7552b 1

end CertificateChecks.PresLetters7552

namespace Certificates

open CertificateChecks.PresLetters7552 in
open CFSG CFSG.ASVolI CFSG.CosetTable in
theorem certificate7552 : ∀ k < 98, Finite (PG 5 (burnsideF48s_u42eWs k)) ∧
    Nat.card (PG 5 (burnsideF48s_u42eWs k)) ≤
      (if k ∈ [0, 5, 8, 11, 17, 22, 27, 67, 73, 77, 83] then 45 else 1) * 1152 := fun k hk =>
  TableFact.card_restrict (burnsideF48s_u42eWs k) (by norm_num) (subsetOf 5 [0, 1, 2, 4])
    (by decide) (idx k hk) (res k hk)

end Certificates
