module

public import Certificates.Data.Kernel.WordsS
public import Certificates.Data.Kernel.OrbK
public import Certificates.Data.Kernel.AlphaGrpK
public import Certificates.Data.Kernel.AlphaFunK
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaFi24Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelAM.Fi24

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.AlphaFi24 CFSG.KC.Ord CFSG.KC.WordsS CFSG.KC.OrbK

theorem w_mats :
    fi24Mod.acts.all (fun g => decide (g.mat.length = fi24Mod.basis.length * fi24Mod.basis.length)) =
      true := by
  decide +kernel

theorem w_orb : orbK 3 12 fi24Mod (fi24Mod.indep.map (·.1)) fi24Orb = true := by
  decide +kernel

theorem w_pc : pcWf (fi24Tops ++ fi24Mod.basisPc 3) = true := by decide +kernel

theorem w_top : fi24Tops.all (fun q => fi24Mod.acts.any (·.reg == q.reg)) = true := by
  decide +kernel

theorem w_wTops : fi24Tidx.all (fun i => decide (i < fi24Mod.acts.length) &&
    fi24Tops.any (·.reg == (fi24Mod.acts.getD i default).reg)) = true := by
  decide +kernel

theorem w_words : wNodupS 7 4 49 562949953421311 127 4432676798593 282578800148737 2225029922430
    (keyS 49 [4, 9, 11, 17, 23, 27, 29, 38, 41])
    (fi24Tidx.map fun i => (fi24Mod.acts.getD i default).mat) = true := by
  decide +kernel

theorem w_fun : funW 3 fi24Mod 7 11 539 fi24CfSp = true := by decide +kernel

theorem w_alt : altW 3 fi24Mod 7 11 26411 2401 fi24CiSp fi24CtSp tgtAlt = true := by
  decide +kernel

end CertificateChecks.KernelAM.Fi24

end
