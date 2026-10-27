module

public import CFSG.Sporadic.Recognition.LyonsFinalModularInputs
public import CFSG.Sporadic.Recognition.LyonsFinalCore107
import Certificates.Certificate6114
import Certificates.Kernel.LyDce.Twist
import Certificates.Kernel.LyGlue.Bind
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Recognition.LyonsModelCert

public section

open CFSG.Sporadic.Recognition.LyonsSims

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Recognition.LyonsSims.LyFinal CFSG.CosetTable in
theorem certificate6118 : 
    (genSub {r : FreeGroup (Fin 6) | r ∈ (modularR Rcore107 modularD).map FreeGroup.mk}
        (subsetOf 6 [0, 1])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 6) | r ∈ (modularR Rcore107 modularD).map FreeGroup.mk}
        (subsetOf 6 [0, 1])).index ≤ 9606125 :=
  KernelLyDce.index_cd (KernelLy.cL_eq Ly0.tabCheck_eq_true) (KernelLy.dL_eq Ly0.tabCheck_eq_true)
    certificate6114

end Certificates
