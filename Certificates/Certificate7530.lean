module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.Milestones.ASVolI.F48.Small.Sp42Inputs
import Certificates.Kernel.PresLetters.F7530
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Data.Kernel.Bounds.TableFact

public section

open CFSG CFSG.ASVolI CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates

namespace CertificateChecks.PresLetters7530

#kc_forall_chunks idx (fun j => KB.TableFact 5 ((burnsideF48s_sp42Ws j).map encW)
  ((subsetOf 5 [0, 1, 2, 3]).map fun x => [(x.val, true)]) (if j = 1 then 15 else 1))
  4 CFSG.KBFact.F7530a 1

#kc_forall_chunks res (fun j => KB.TableFact (subsetOf 5 [0, 1, 2, 3]).length
  ((burnsideF48s_sp42WsA j).map encW) [] 48) 4 CFSG.KBFact.F7530b 1

end CertificateChecks.PresLetters7530

namespace Certificates

open CertificateChecks.PresLetters7530 in
open CFSG CFSG.ASVolI CFSG.CosetTable in
theorem certificate7530 : ∀ j < 4, Finite (PG 5 (burnsideF48s_sp42Ws j)) ∧
    Nat.card (PG 5 (burnsideF48s_sp42Ws j)) ≤ if j = 1 then 720 else 48 := fun j hj => by
  obtain ⟨f, c⟩ := TableFact.card_restrict (burnsideF48s_sp42Ws j) (by norm_num)
    (subsetOf 5 [0, 1, 2, 3]) (by decide) (idx j hj) (res j hj)
  refine ⟨f, c.trans ?_⟩
  split_ifs <;> norm_num

end Certificates
