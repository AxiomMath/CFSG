module

public import CFSG.Certificates.CosetTablePresented
public import Certificates.Data.M13L33Rels
import Certificates.Kernel.PresLetters.F17633
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import Mathlib.Algebra.Order.Ring.Star

public section

open CFSG.CosetTable CFSG.HardMathSupport.Dickson.BMRows.M13L33 CFSG.KC.MiscCoset

namespace Certificates

open CFSG.CosetTable CFSG.HardMathSupport.Dickson.BMRows.M13L33 in
theorem certificate17633 : Finite (PG 2 l33Rels) ∧ Nat.card (PG 2 l33Rels) ≤ 5616 :=
  card_le_of_zpowers_index l33Rels [(1, true)] (k := 13) (by norm_num) (by decide)
    (TableFact.zpowers_index l33Rels (by norm_num) [(1, true)] CFSG.KBFact.F17633)

end Certificates
