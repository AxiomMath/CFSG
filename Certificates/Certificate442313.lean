module

import Certificates.Kernel.PresLetters.F442313
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.Certificates.CosetTablePresented
public import Certificates.Data.Y2L.Words

public section

open CFSG.OddStandard.HigherRank.G2Three.Sec2 CFSG.KC.MiscCoset

namespace Certificates

open CFSG.OddStandard.HigherRank.G2Three.Sec2 in
theorem certificate442313 : (Finite (CFSG.CosetTable.PG 5 (y2l_ws26 2 false)) ∧
      Nat.card (CFSG.CosetTable.PG 5 (y2l_ws26 2 false)) ≤ 512) ∧
    (Finite (CFSG.CosetTable.PG 5 (y2l_ws26 2 true)) ∧
      Nat.card (CFSG.CosetTable.PG 5 (y2l_ws26 2 true)) ≤ 512) ∧
    (Finite (CFSG.CosetTable.PG 5 (y2l_ws26 1 true)) ∧
      Nat.card (CFSG.CosetTable.PG 5 (y2l_ws26 1 true)) ≤ 64) :=
  ⟨TableFact.card (y2l_ws26 2 false) (by norm_num) CFSG.KBFact.F442313a,
    TableFact.card (y2l_ws26 2 true) (by norm_num) CFSG.KBFact.F442313b,
    TableFact.card (y2l_ws26 1 true) (by norm_num) CFSG.KBFact.F442313c⟩

end Certificates
