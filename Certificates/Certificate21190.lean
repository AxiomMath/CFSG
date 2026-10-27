module

public import CFSG.CGT.M24R.M24Enum
import Certificates.Kernel.PresLetters.F21190
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CGT.M24R CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates

namespace Certificates

open CFSG.CGT.M24R in
theorem certificate21190 : n8Sub.FiniteIndex ∧ n8Sub.index ≤ 759 :=
  TableFact.genSub_index m24Rels (by norm_num) (subsetOf 11 (List.range 10)) CFSG.KBFact.F21190

end Certificates
