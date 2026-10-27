module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenRels
import Certificates.Kernel.CosPres.F291420
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.KC.MiscCoset
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven

namespace Certificates

open CFSG.CosetTable
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven in
theorem certificate291420 : Finite (PG 4 l37Rels) ∧ Nat.card (PG 4 l37Rels) ≤ 1876896 :=
  TableFact.card_restrict l37Rels (by norm_num) (subsetOf 4 [0, 1, 2]) (by decide)
    CFSG.KBFact.F291420a CFSG.KBFact.F291420b

end Certificates
