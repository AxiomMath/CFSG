module

public import Certificates.Kernel.CoreD2K.Co3.Data
public import Certificates.Data.Kernel.CoreD2K.Check
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.CoreD2Co3
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 10

namespace CertificateChecks.KernelCoreD2K.Co3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.CoreD2K
open Certificates.CoreD2Perm

theorem k_sz : szOK 276 9 = true := by quickRfl
theorem k_gens : gensK 276 9 co3LinesData GP GPI RE.G GT GTI = true := by quickRfl
theorem k_ek : Nat.beq RE.k co3LinesData.base.eW.length = true := by quickRfl
theorem k_eh : penumHdK (pidn 276 9) RE.cnt 125 RE.T RE.PL = true := by quickRfl
theorem k_ecnt : Nat.beq RE.cnt 125 = true := by quickRfl
theorem k_esl : penumSlK 276 9 (mask 9) (276 * 9) false RE.G RE.GI RE.k RE.cnt RE.T RE.PL RE.POS
    RE.SRT RE.SRI 0 125 = true := by quickRfl
theorem k_nab : nabK 276 9 co3LinesData.base.eW.length RE.G = true := by quickRfl
theorem k_cen : cenK 276 9 5 co3LinesData.base.eW.length RE.G = true := by quickRfl
theorem k_lines : linesK 276 9 5 co3LinesData RE.G = true := by quickRfl
theorem k_kinds : kindsK 276 9 co3LinesData RE.G GT = true := by quickRfl
theorem k_words : wordsK 276 9 co3LinesData GP GT GTI = true := by quickRfl

end CertificateChecks.KernelCoreD2K.Co3

end
