module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Data.Kernel.AlphaGrpK
public import Certificates.Kernel.LocalComp.ThOrder
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaThData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordDefs

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelAG

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaTh

theorem th_K : mcertN (opsF2K 248) KernelLC.ThA.M KernelLC.ThB.M
    ⟨thNregs, thProg, thMod.modFactsW 3 thTops⟩ = true := by
  quickRfl

theorem th_wf : thMod.wf 3 = true := by decide +kernel

theorem th_pc : pcWf (thTops ++ thMod.basisPc 3) = true := by decide +kernel

theorem th_top : thTops.all (fun q => thMod.acts.any (·.reg == q.reg)) = true := by
  decide +kernel

theorem th_wTops : thTidx.all (fun i => decide (i < thMod.acts.length) &&
    thTops.any (·.reg == (thMod.acts.getD i default).reg)) = true := by
  decide +kernel

theorem th_wNodup : ((wordsL 3 thMod.basis.length
    (thTidx.map fun i => (thMod.acts.getD i default).mat)).map (codeL 3)).Nodup := by
  decide +kernel

theorem th_wCount : decide (3 ^ 10 ≤ (wordsL 3 thMod.basis.length
    (thTidx.map fun i => (thMod.acts.getD i default).mat)).length * 3 ^ thMod.basis.length) =
    true := by
  decide +kernel

theorem th_fun : thMod.funOK 3 thCf = true := by decide +kernel

theorem th_alt : altW 3 thMod 5 7 4375 625 thCiSp thCtSp tgtAlt = true := by decide +kernel

end CertificateChecks.KernelAG

end
