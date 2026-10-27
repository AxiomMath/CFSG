module

public import Certificates.Data.H13.U42AutP10Rel
public import CFSG.Certificates.CosetTablePresented
import Certificates.Kernel.PresLetters.F4165A
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.Quasithin.H13.F431.U42Aut CFSG.KC.MiscCoset

namespace Certificates

open CFSG.CosetTable CFSG.Quasithin.H13.F431.U42Aut in
theorem certificate4165 : Finite (PG 7 p10Ws) ∧ Nat.card (PG 7 p10Ws) ≤ 6065280 := by
  obtain ⟨f, c⟩ := TableFact.card_restrict p10Ws (by norm_num) (subsetOf 7 [0, 1, 2, 3, 4, 5])
    (by decide) CFSG.KBFact.F4165a CFSG.KBFact.F4165b
  exact ⟨f, c.trans (by norm_num)⟩

end Certificates
