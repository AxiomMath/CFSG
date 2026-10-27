module

public import Certificates.Data.Kernel.AlphaGrpK
public import Certificates.Data.Kernel.AlphaFunK
public import Certificates.Kernel.TcGen.Fi22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaFi22Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelAM

open CFSG.KC.OpsLayK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaFi22

theorem fi22_K : mcertL KernelTc.Fi22.lay KernelTc.Fi22.A KernelTc.Fi22.B
    ⟨fi22Nregs, fi22Prog, fi22Mod.modFactsE 3 fi22Tops fi22Gs⟩ = true := by
  quickRfl

theorem fi22_wf : fi22Mod.wf 3 = true := by decide +kernel

theorem fi22_pc : pcWf (fi22Tops ++ fi22Mod.basisPc 3) = true := by decide +kernel

theorem fi22_ent : fi22Mod.acts.all (fun g => g.mat.all (· < 3)) = true := by decide +kernel

theorem fi22_top : fi22Tops.all (fun q => fi22Mod.acts.any (·.reg == q.reg)) = true := by
  decide +kernel

theorem fi22_grp : fi22Mod.grpOK fi22Tops fi22Gs = true := by decide +kernel

theorem fi22_fun : funW 3 fi22Mod 5 83 2075 fi22CfSp = true := by decide +kernel

theorem fi22_alt : altW 3 fi22Mod 5 83 51875 625 fi22CiSp fi22CtSp tgtAlt = true := by
  decide +kernel

end CertificateChecks.KernelAM

end
