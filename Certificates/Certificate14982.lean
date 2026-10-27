module

public import CFSG.CGT.T75JM.M22PresInputs
import Certificates.Kernel.CosPresTab.F14982
import Certificates.Kernel.CosPresTab.M22Glue
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.CGT.T75JM

namespace Certificates

open CFSG.CosetTable CFSG.CGT.T75JM in
theorem certificate14982 : (Finite (PG 7 m22Rels) ∧ Nat.card (PG 7 m22Rels) ≤ 443520) ∧ m22TabCheck = true := by
  refine ⟨?_, CFSG.KC.TabWord.M22.m22TabCheck_eq_true⟩
  have c2 := TableFact.card m22RelsK (by decide) CFSG.KBFact.F14982c
  have c6 := card_le_of_index_restrict m22RelsN6
    (subsetOf (subsetOf 7 [0, 1, 2, 3, 4, 5]).length [0, 1]) (TableFact.genSub_index m22RelsN6 (by decide) _ CFSG.KBFact.F14982b) c2
  have c7 := card_le_of_index_restrict m22Rels (subsetOf 7 [0, 1, 2, 3, 4, 5])
    (TableFact.genSub_index m22Rels (by decide) _ CFSG.KBFact.F14982a) c6
  exact c7

end Certificates
