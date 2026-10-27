module

import Certificates.Kernel.CosPres.F21202
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.Certificates.CosetTablePresented
public import CFSG.LargeExtraspecial.AS62Rels

public section

open CFSG.CosetTable CFSG.LargeExtraspecial.AS62 CFSG.KC.MiscCoset

namespace Certificates

open CFSG.CosetTable CFSG.LargeExtraspecial.AS62 in
theorem certificate21202 : (Finite (PG 4 relsB) ∧ Nat.card (PG 4 relsB) ≤ 192) ∧
    (Finite (PG 5 rels1) ∧ Nat.card (PG 5 rels1) ≤ 576) ∧
    (Finite (PG 5 rels2) ∧ Nat.card (PG 5 rels2) ≤ 960) := by
  obtain ⟨fB, cB⟩ := TableFact.card_restrict relsB (by norm_num) (subsetOf 4 [2, 3]) (by decide)
    CFSG.KBFact.F21202a CFSG.KBFact.F21202b
  obtain ⟨f1, c1⟩ := TableFact.card_restrict rels1 (by norm_num) (subsetOf 5 [2, 3]) (by decide)
    CFSG.KBFact.F21202c CFSG.KBFact.F21202d
  obtain ⟨f2, c2⟩ := TableFact.card_restrict rels2 (by norm_num) (subsetOf 5 [2, 3]) (by decide)
    CFSG.KBFact.F21202e CFSG.KBFact.F21202f
  exact ⟨⟨fB, cB.trans (by norm_num)⟩, ⟨f1, c1.trans (by norm_num)⟩, ⟨f2, c2.trans (by norm_num)⟩⟩

end Certificates
