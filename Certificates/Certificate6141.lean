module

public import CFSG.Certificates.CosetTablePresented
public import Certificates.Data.ONanF2Pres
import Certificates.Kernel.PresLetters.F6141
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import Mathlib.Algebra.Order.Ring.Star

public section

open CFSG.OddStandard.ONanRec.F2 CFSG.CosetTable

namespace Certificates

open CFSG.OddStandard.ONanRec.F2 CFSG.CosetTable in
theorem certificate6141 : Finite (PG 5 alpRels) ∧ Nat.card (PG 5 alpRels) ≤ 512 :=
  CFSG.KC.MiscCoset.TableFact.card alpRels (by norm_num) CFSG.KBFact.F6141

end Certificates
