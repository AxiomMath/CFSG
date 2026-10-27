module

public import Certificates.Data.L28Presentation
public import CFSG.Certificates.CosetTablePresented
import Certificates.Kernel.PresLetters.F17371
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import Mathlib.Algebra.Order.Ring.Star

public section

open CFSG.CosetTable CFSG.HardMathSupport.Dickson.I271.L28Presentation CFSG.KC.MiscCoset

namespace Certificates

open CFSG.CosetTable CFSG.HardMathSupport.Dickson.I271.L28Presentation in
theorem certificate17371 : Finite (PG 2 l28Words) ∧ Nat.card (PG 2 l28Words) ≤ 504 :=
  card_le_of_zpowers_index l28Words [(0, true)] (k := 2) (by norm_num) (by decide)
    (TableFact.zpowers_index l28Words (by norm_num) [(0, true)] CFSG.KBFact.F17371)

end Certificates
