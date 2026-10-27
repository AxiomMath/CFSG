module

public import CFSG.CGT.T75JM.M22PDInputs
import Certificates.Kernel.CosPresTab.F14982
import Certificates.Kernel.CosPresTab.M22Glue
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.CGT.T75JM

namespace Certificates

open CFSG.CosetTable CFSG.CGT.T75JM in
theorem certificate14989 :
    ((genSub {r : FreeGroup (Fin 7) | r ∈ m22RelsPD.map FreeGroup.mk}
        (subsetOf 7 [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 7) | r ∈ m22RelsPD.map FreeGroup.mk}
        (subsetOf 7 [0, 1, 2, 3, 4, 5])).index ≤ 77) ∧
    thetaTabCheck = true :=
  ⟨TableFact.genSub_index m22RelsPD (by decide) _ CFSG.KBFact.F14989a,
    CFSG.KC.TabWord.M22.thetaTabCheck_eq_true⟩

end Certificates
