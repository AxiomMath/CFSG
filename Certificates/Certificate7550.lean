module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.Milestones.ASVolI.F48.Small.Sp43eInputs
import Certificates.Kernel.PresLetters.F7550
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Data.Kernel.Bounds.TableFact

public section

open CFSG CFSG.ASVolI CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates

namespace CertificateChecks.PresLetters7550

#kc_forall_chunks idx (fun k => KB.TableFact 5 ((burnsideF48s_sp43eWs k).map encW)
  ((subsetOf 5 [0, 1, 2, 4]).map fun x => [(x.val, true)]) (if k % 4 = 0 then 40 else 1))
  32 CFSG.KBFact.F7550a 1

#kc_forall_chunks res (fun k => KB.TableFact (subsetOf 5 [0, 1, 2, 4]).length
  ((burnsideF48s_sp43eWsB k).map encW) [] 1296) 32 CFSG.KBFact.F7550b 1

end CertificateChecks.PresLetters7550

namespace Certificates

open CertificateChecks.PresLetters7550 in
open CFSG CFSG.ASVolI CFSG.CosetTable in
theorem certificate7550 : ∀ k < 32, Finite (PG 5 (burnsideF48s_sp43eWs k)) ∧
    Nat.card (PG 5 (burnsideF48s_sp43eWs k)) ≤ (if k % 4 = 0 then 40 else 1) * 1296 := fun k hk =>
  TableFact.card_restrict (burnsideF48s_sp43eWs k) (by norm_num) (subsetOf 5 [0, 1, 2, 4])
    (by decide) (idx k hk) (res k hk)

end Certificates
