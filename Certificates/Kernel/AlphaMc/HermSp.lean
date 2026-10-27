module

public import Certificates.Data.Kernel.AlphaAltSp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SU6Data
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SF4Data

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelAM

open CFSG.AGLEmbedding.R3

theorem u6F_K : CFSG.LocalAnalysis.GLTheoremA.U6Herm.u6Mod.funOK 2
    CFSG.LocalAnalysis.GLTheoremA.U6Herm.u6Cf = true := by
  decide +kernel

theorem u6A_K : altSp 2 CFSG.LocalAnalysis.GLTheoremA.U6Herm.u6Mod 9
    CFSG.LocalAnalysis.GLTheoremA.U6Herm.u6CiSupp tgtAlt = true := by
  decide +kernel

theorem f4F_K : CFSG.LocalAnalysis.GLTheoremA.F4Sym.f4Mod.funOK 2
    CFSG.LocalAnalysis.GLTheoremA.F4Sym.f4Cf = true := by
  decide +kernel

theorem f4A_K : altSp 2 CFSG.LocalAnalysis.GLTheoremA.F4Sym.f4Mod 10
    CFSG.LocalAnalysis.GLTheoremA.F4Sym.f4CiSupp tgtAlt = true := by
  decide +kernel

end CertificateChecks.KernelAM

end
