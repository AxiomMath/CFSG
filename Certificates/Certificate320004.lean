module

public import Certificates.Data.G23RecogWordsInputs
import Certificates.Kernel.PresLetters.F320004A
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable CFSG.KC.MiscCoset

namespace Certificates

open CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable in
theorem certificate320004 : ((genSub {r : FreeGroup (Fin 6) | r ∈ g23Words.map FreeGroup.mk}
        (subsetOf 6 [0, 1, 2, 3, 4])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 6) | r ∈ g23Words.map FreeGroup.mk}
        (subsetOf 6 [0, 1, 2, 3, 4])).index ≤ 7371)
    ∧ (Finite (PG (subsetOf 6 [0, 1, 2, 3, 4]).length
          (restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) g23Words)) ∧
        Nat.card (PG (subsetOf 6 [0, 1, 2, 3, 4]).length
          (restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) g23Words)) ≤ 576)
    ∧ (Finite (PG 2 g23PD) ∧ Nat.card (PG 2 g23PD) ≤ 192)
    ∧ (Finite (PG 3 g23PM) ∧ Nat.card (PG 3 g23PM) ≤ 1344) :=
  ⟨TableFact.genSub_index g23Words (by norm_num) (subsetOf 6 [0, 1, 2, 3, 4]) CFSG.KBFact.F320004a,
    TableFact.card (restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) g23Words) (by decide)
      CFSG.KBFact.F320004b,
    TableFact.card g23PD (by norm_num) CFSG.KBFact.F320004c,
    TableFact.card g23PM (by norm_num) CFSG.KBFact.F320004d⟩

end Certificates
