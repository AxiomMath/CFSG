module

public import Certificates.Data.Coxeter555
import Certificates.Kernel.PresLetters.F442151
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.EvenSporadicStandard.HNRecog.Coxeter555 CFSG.KC.MiscCoset

namespace Certificates

open CFSG.CosetTable CFSG.EvenSporadicStandard.HNRecog.Coxeter555 in
theorem certificate442151 : Finite (PG 3 rels555) ∧ Nat.card (PG 3 rels555) ≤ 660 :=
  card_le_of_zpowers_index rels555 axWord (k := 5) (by norm_num) (by decide)
    (TableFact.zpowers_index rels555 (by norm_num) axWord CFSG.KBFact.F442151)

end Certificates
