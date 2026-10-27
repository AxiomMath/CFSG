module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Data.Kernel.AlphaGrpK
public import Certificates.Kernel.J3Local.Seeds
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaJ3Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelAG

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaJ3

theorem j3_K : mcertN (opsF2K 80) KernelJ3L.JA.M KernelJ3L.JB.M
    ⟨j3Nregs, j3Prog, j3Mod.modFactsE 3 j3Tops j3Gs⟩ = true := by
  quickRfl

theorem j3_wf : j3Mod.wf 3 = true := by decide +kernel

theorem j3_pc : pcWf (j3Tops ++ j3Mod.basisPc 3) = true := by decide +kernel

theorem j3_ent : j3Mod.acts.all (fun g => g.mat.all (· < 3)) = true := by decide +kernel

theorem j3_top : j3Tops.all (fun q => j3Mod.acts.any (·.reg == q.reg)) = true := by
  decide +kernel

theorem j3_grp : j3Mod.grpOK j3Tops j3Gs = true := by decide +kernel

theorem j3_fun : j3Mod.funOK 3 j3Cf = true := by decide +kernel

theorem j3_alt : altW 3 j3Mod 3 11 891 81 j3CiSp j3CtSp tgtAlt = true := by decide +kernel

end CertificateChecks.KernelAG

end
