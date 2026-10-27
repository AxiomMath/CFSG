module

public import Certificates.Kernel.CoreD2K.J2.Data
public import Certificates.Data.Kernel.CoreD2K.Check
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.CoreD2J2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 10

namespace CertificateChecks.KernelCoreD2K.J2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.CoreD2K
open Certificates.CoreD2Perm

theorem k_sz : szOK 315 9 = true := by quickRfl
theorem k_gens : gensK 315 9 j2LinesData GP GPI RE.G GT GTI = true := by quickRfl
theorem k_ek : Nat.beq RE.k j2LinesData.base.eW.length = true := by quickRfl
theorem k_eh : penumHdK (pidn 315 9) RE.cnt 27 RE.T RE.PL = true := by quickRfl
theorem k_ecnt : Nat.beq RE.cnt 27 = true := by quickRfl
theorem k_esl : penumSlK 315 9 (mask 9) (315 * 9) false RE.G RE.GI RE.k RE.cnt RE.T RE.PL RE.POS
    RE.SRT RE.SRI 0 27 = true := by quickRfl
theorem k_nab : nabK 315 9 j2LinesData.base.eW.length RE.G = true := by quickRfl
theorem k_cen : cenK 315 9 3 j2LinesData.base.eW.length RE.G = true := by quickRfl
theorem k_lines : linesK 315 9 3 j2LinesData RE.G = true := by quickRfl
theorem k_kinds : kindsK 315 9 j2LinesData RE.G GT = true := by quickRfl
theorem k_words : wordsK 315 9 j2LinesData GP GT GTI = true := by quickRfl

end CertificateChecks.KernelCoreD2K.J2

end
