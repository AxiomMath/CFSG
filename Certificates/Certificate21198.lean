module

import Certificates.Kernel.CosPres.F21198
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.CGT.A8S.RelData
public import CFSG.Certificates.CosetTablePresented

public section

open CFSG.CosetTable CFSG.CGT.A8S CFSG.KC.MiscCoset

namespace Certificates

open CFSG.CosetTable CFSG.CGT.A8S in
theorem certificate21198 : Finite (PG 5 relsN0A8) ∧ Nat.card (PG 5 relsN0A8) ≤ 1344 := by
  obtain ⟨f, c⟩ := TableFact.card_restrict relsN0A8 (by norm_num) (subsetOf 5 [0, 1]) (by decide)
    CFSG.KBFact.F21198b CFSG.KBFact.F21198a
  exact ⟨f, c.trans (by norm_num)⟩

end Certificates
