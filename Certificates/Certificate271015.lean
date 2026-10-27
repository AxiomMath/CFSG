module

public import CFSG.CGT.T75M23.M23PresInputs
import Certificates.Kernel.CosPresTab.F271015
import Certificates.Kernel.CosPresTab.M23Glue
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.CGT.T75M23

namespace Certificates

open CFSG.CosetTable CFSG.CGT.T75M23 in
theorem certificate271015 : (Finite (PG 7 m23Rels) ∧ Nat.card (PG 7 m23Rels) ≤ 10200960) ∧ m23TabCheck = true := by
  refine ⟨?_, CFSG.KC.TabWord.M23.m23TabCheck_eq_true⟩
  have c2 := TableFact.card m23RelsK (by decide) CFSG.KBFact.F271015c
  have c6 := card_le_of_index_restrict m23RelsN6
    (subsetOf (subsetOf 7 [0, 1, 2, 3, 4, 5]).length [0, 1])
    (TableFact.genSub_index m23RelsN6 (by decide) _ CFSG.KBFact.F271015b) c2
  have c7 := card_le_of_index_restrict m23Rels (subsetOf 7 [0, 1, 2, 3, 4, 5])
    (TableFact.genSub_index m23Rels (by decide) _ CFSG.KBFact.F271015a) c6
  exact c7

end Certificates
