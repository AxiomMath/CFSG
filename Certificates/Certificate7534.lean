module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.Milestones.ASVolI.F48.Small.G22Inputs
import Certificates.Kernel.PresLetters.F7534
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Data.Kernel.Bounds.TableFact

public section

open CFSG CFSG.ASVolI CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates

namespace CertificateChecks.PresLetters7534

#kc_forall_chunks idx (fun j => KB.TableFact 6 ((burnsideF48s_g22Ws j).map encW)
  ((subsetOf 6 [0, 1, 2, 4, 5]).map fun x => [(x.val, true)]) (if j = 1 then 63 else 1))
  4 CFSG.KBFact.F7534a 1

#kc_forall_chunks res (fun j => KB.TableFact (subsetOf 6 [0, 1, 2, 4, 5]).length
  ((burnsideF48s_g22WsB j).map encW) [] 192) 4 CFSG.KBFact.F7534b 1

end CertificateChecks.PresLetters7534

namespace Certificates

open CertificateChecks.PresLetters7534 in
open CFSG CFSG.ASVolI CFSG.CosetTable in
theorem certificate7534 : ∀ j < 4, Finite (PG 6 (burnsideF48s_g22Ws j)) ∧
    Nat.card (PG 6 (burnsideF48s_g22Ws j)) ≤ if j = 1 then 12096 else 192 := fun j hj => by
  obtain ⟨f, c⟩ := TableFact.card_restrict (burnsideF48s_g22Ws j) (by norm_num)
    (subsetOf 6 [0, 1, 2, 4, 5]) (by decide) (idx j hj) (res j hj)
  refine ⟨f, c.trans ?_⟩
  split_ifs <;> norm_num

end Certificates
