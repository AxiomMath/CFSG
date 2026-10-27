module

public import Certificates.Data.U42Presentation
public import CFSG.Certificates.CosetTablePresented
import Certificates.Kernel.U42KB.Table
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import Mathlib.Algebra.Order.Ring.Star

public section

open CFSG.HardMathSupport.Dickson.I271.U42Presentation

namespace Certificates

open CFSG.HardMathSupport.Dickson.I271.U42Presentation in
theorem certificate17350 : Finite (CFSG.CosetTable.PG 2 u42Words) ∧ Nat.card (CFSG.CosetTable.PG 2 u42Words) ≤ 25920 :=
  CFSG.KC.MiscCoset.TableFact.card u42Words (by norm_num) CFSG.KBFact.K17350

end Certificates
