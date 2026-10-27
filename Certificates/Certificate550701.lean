module

public import Certificates.Data.YamakiPres
import Certificates.Kernel.CosPres.F550701
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.Certificates.CosetTablePresented

public section

open CFSG.CosetTable CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KC.MiscCoset

namespace Certificates

open CFSG.CosetTable CFSG.ClassicalInvolution.Solomon73.Yamaki in
theorem certificate550701 : Finite (PG 12 (yamakiRels ())) ∧ Nat.card (PG 12 (yamakiRels ())) ≤ 1451520 := by
  obtain ⟨f, c⟩ := TableFact.card_restrict (yamakiRels ()) (by norm_num)
    (subsetOf 12 [0, 1, 2, 3, 4, 5, 6, 7, 8]) (by decide) CFSG.KBFact.F550701b
    CFSG.KBFact.F550701a
  exact ⟨f, c.trans (by norm_num)⟩

end Certificates
