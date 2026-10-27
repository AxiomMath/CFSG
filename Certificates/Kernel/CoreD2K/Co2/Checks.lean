module

public import Certificates.Kernel.CoreD2K.Co2.Data
public import Certificates.Data.Kernel.CoreD2K.Check
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.CoreD2Co2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 10

namespace CertificateChecks.KernelCoreD2K.Co2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.CoreD2K
open Certificates.CoreD2Perm

theorem k_sz : szOK 2300 12 = true := by quickRfl
theorem k_gens : gensK 2300 12 co2LinesData GP GPI RE.G GT GTI = true := by quickRfl
theorem k_ek : Nat.beq RE.k co2LinesData.base.eW.length = true := by quickRfl
theorem k_eh : penumHdK (pidn 2300 12) RE.cnt 125 RE.T RE.PL = true := by quickRfl
theorem k_ecnt : Nat.beq RE.cnt 125 = true := by quickRfl
theorem k_esl : penumSlK 2300 12 (mask 12) (2300 * 12) false RE.G RE.GI RE.k RE.cnt RE.T RE.PL
    RE.POS RE.SRT RE.SRI 0 125 = true := by quickRfl
theorem k_nab : nabK 2300 12 co2LinesData.base.eW.length RE.G = true := by quickRfl
theorem k_cen : cenK 2300 12 5 co2LinesData.base.eW.length RE.G = true := by quickRfl
theorem k_lines : linesK 2300 12 5 co2LinesData RE.G = true := by quickRfl
theorem k_kinds : kindsK 2300 12 co2LinesData RE.G GT = true := by quickRfl
theorem k_words : wordsK 2300 12 co2LinesData GP GT GTI = true := by quickRfl

end CertificateChecks.KernelCoreD2K.Co2

end
