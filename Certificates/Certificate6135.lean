module

public import Certificates.Data.ChengHeldONRels
public import CFSG.Certificates.CosetTablePresented
import Certificates.Kernel.PresLetters.F6135
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import Mathlib.Algebra.Order.Ring.Star

public section

open CFSG.OddStandard.ChengHeld.ONSylow CFSG.CosetTable

namespace Certificates

open CFSG.OddStandard.ChengHeld.ONSylow CFSG.CosetTable in
theorem certificate6135 : Finite (PG 8 onRels) ∧ Nat.card (PG 8 onRels) ≤ 512 :=
  CFSG.KC.MiscCoset.TableFact.card onRels (by norm_num) CFSG.KBFact.PL6135

end Certificates
