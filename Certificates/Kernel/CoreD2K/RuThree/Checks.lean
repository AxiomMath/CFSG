module

public import Certificates.Kernel.CoreD2K.RuThree.Data
public import Certificates.Data.Kernel.CoreD2K.Check
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.CoreD2RuThree
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 10

namespace CertificateChecks.KernelCoreD2K.RuThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.CoreD2K
open Certificates.CoreD2Perm

theorem k_sz : szOK 4060 12 = true := by quickRfl
theorem k_gens : gensK 4060 12 ruThreeLinesData GP GPI RE.G GT GTI = true := by quickRfl
theorem k_ek : Nat.beq RE.k ruThreeLinesData.base.eW.length = true := by quickRfl
theorem k_eh : penumHdK (pidn 4060 12) RE.cnt 27 RE.T RE.PL = true := by quickRfl
theorem k_ecnt : Nat.beq RE.cnt 27 = true := by quickRfl
theorem k_esl : penumSlK 4060 12 (mask 12) (4060 * 12) false RE.G RE.GI RE.k RE.cnt RE.T RE.PL
    RE.POS RE.SRT RE.SRI 0 27 = true := by quickRfl
theorem k_nab : nabK 4060 12 ruThreeLinesData.base.eW.length RE.G = true := by quickRfl
theorem k_cen : cenK 4060 12 3 ruThreeLinesData.base.eW.length RE.G = true := by quickRfl
theorem k_lines : linesK 4060 12 3 ruThreeLinesData RE.G = true := by quickRfl
theorem k_kinds : kindsK 4060 12 ruThreeLinesData RE.G GT = true := by quickRfl
theorem k_words : wordsK 4060 12 ruThreeLinesData GP GT GTI = true := by quickRfl

end CertificateChecks.KernelCoreD2K.RuThree

end
