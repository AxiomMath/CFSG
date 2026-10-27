module

public import Certificates.Data.G23RecogWordsInputs
import Certificates.Kernel.PresLetters.F320006
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

namespace Certificates

open CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable in
theorem certificate320006 : (genSub {r : FreeGroup (Fin 3) | r ∈ g23PM.map FreeGroup.mk} (subsetOf 3 [0, 1])).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin 3) | r ∈ g23PM.map FreeGroup.mk} (subsetOf 3 [0, 1])).index ≤ 7 :=
  CFSG.KC.MiscCoset.TableFact.genSub_index g23PM (by norm_num) (subsetOf 3 [0, 1])
    CFSG.KBFact.F320006

end Certificates
