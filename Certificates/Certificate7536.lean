module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.Milestones.ASVolI.F48.Small.Sp43Inputs
import Certificates.Kernel.PresLetters.F7536
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Data.Kernel.Bounds.TableFact

public section

open CFSG CFSG.ASVolI CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates

namespace CertificateChecks.PresLetters7536

#kc_forall_chunks idx (fun k => KB.TableFact 4 ((burnsideF48s_sp43Ws k).map encW)
  ((subsetOf 4 [0, 1, 2]).map fun x => [(x.val, true)]) (if k % 2 = 0 then 40 else 1))
  8 CFSG.KBFact.F7536a 1

#kc_forall_chunks res (fun k => KB.TableFact (subsetOf 4 [0, 1, 2]).length
  ((burnsideF48s_sp43WsB k).map encW) [] 648) 8 CFSG.KBFact.F7536b 1

end CertificateChecks.PresLetters7536

namespace Certificates

open CertificateChecks.PresLetters7536 in
open CFSG CFSG.ASVolI CFSG.CosetTable in
theorem certificate7536 : ∀ k < 8, Finite (PG 4 (burnsideF48s_sp43Ws k)) ∧
    Nat.card (PG 4 (burnsideF48s_sp43Ws k)) ≤ (if k % 2 = 0 then 40 else 1) * 648 := fun k hk =>
  TableFact.card_restrict (burnsideF48s_sp43Ws k) (by norm_num) (subsetOf 4 [0, 1, 2])
    (by decide) (idx k hk) (res k hk)

end Certificates
