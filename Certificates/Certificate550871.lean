module

public import CFSG.Certificates.CosetTablePresented
public import Certificates.Data.E64PresRels
import Certificates.Kernel.PresLetters.F550871
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E64P CFSG.KC.MiscCoset

namespace Certificates

open CFSG.CosetTable CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E64P in
theorem certificate550871 :
    ((genSub {r : FreeGroup (Fin 28) | r ∈ (e64MemberRels ()).map FreeGroup.mk}
        (subsetOf 28 [0, 1])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 28) | r ∈ (e64MemberRels ()).map FreeGroup.mk}
        (subsetOf 28 [0, 1])).index ≤ 1344)
    ∧ (Finite (PG (subsetOf 28 [0, 1]).length
          (restrictWords (subsetOf 28 [0, 1]) (e64MemberRels ()))) ∧
        Nat.card (PG (subsetOf 28 [0, 1]).length
          (restrictWords (subsetOf 28 [0, 1]) (e64MemberRels ()))) ≤ 8) :=
  ⟨TableFact.genSub_index (e64MemberRels ()) (by norm_num) (subsetOf 28 [0, 1]) CFSG.KBFact.F550871a,
    TableFact.card (restrictWords (subsetOf 28 [0, 1]) (e64MemberRels ())) (by decide)
      CFSG.KBFact.F550871b⟩

end Certificates
