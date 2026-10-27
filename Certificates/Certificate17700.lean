module

public import CFSG.HardMathSupport.Dickson.BMRows.M11PresInputs
import Certificates.Kernel.CosPres.F17700
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.HardMathSupport.Dickson.BMRows.M11

namespace Certificates

open CFSG.CosetTable CFSG.HardMathSupport.Dickson.BMRows.M11 in
theorem certificate17700 : Finite (PG 4 m11Rels) ∧ Nat.card (PG 4 m11Rels) ≤ 64 :=
  CFSG.KC.MiscCoset.TableFact.card m11Rels (by norm_num) CFSG.KBFact.F17700a

end Certificates
