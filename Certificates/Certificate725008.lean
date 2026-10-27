module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixFarInputs
import Certificates.Kernel.CosPres.F725008
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.StandardType.QTwo.SixPoint

namespace Certificates

open CFSG.CosetTable CFSG.StandardType.QTwo.SixPoint in
theorem certificate725008 :
    (genSub {r : FreeGroup (Fin 18) | r ∈ (relsP6 ()).map FreeGroup.mk} (subsetOf 18 chart5)).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 18) | r ∈ (relsP6 ()).map FreeGroup.mk} (subsetOf 18 chart5)).index ≤
        2016 :=
  TableFact.genSub_index (relsP6 ()) (by norm_num) (subsetOf 18 chart5) CFSG.KBFact.F725008

end Certificates
