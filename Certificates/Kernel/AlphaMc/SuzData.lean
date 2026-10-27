module

public import Certificates.Data.Kernel.AlphaGrpK
public import Certificates.Data.Kernel.AlphaFunK
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaSuzData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelAM

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.AlphaSuz

@[expose] def nzSp (t : List Nat) : List (Nat × Nat) :=
  (t.zipIdx.filter fun e => e.1 != 0).map fun e => (e.2, e.1)

@[expose] def suzCfSp : List (Nat × Nat) := nzSp suzCfTab

@[expose] def suzCiSp : List (Nat × Nat) := nzSp suzCiTab

theorem suz_cfTab :
    suzCfTab = (suzCfSp.foldl (fun arr x => arr.set! x.1 x.2) (Array.replicate 275 0)).toList := by
  decide +kernel

theorem suz_ciTab :
    suzCiTab = (suzCiSp.foldl (fun arr x => arr.set! x.1 x.2) (Array.replicate 6875 0)).toList := by
  decide +kernel

theorem suz_wf : suzMod.wf 3 = true := by decide +kernel

theorem suz_pc : pcWf (suzTops ++ suzMod.basisPc 3) = true := by decide +kernel

theorem suz_ent : suzMod.acts.all (fun g => g.mat.all (· < 3)) = true := by decide +kernel

theorem suz_top : suzTops.all (fun q => suzMod.acts.any (·.reg == q.reg)) = true := by
  decide +kernel

theorem suz_grp : suzMod.grpOK suzTops suzGs = true := by decide +kernel

theorem suz_fun : funW 3 suzMod 5 11 275 suzCfSp = true := by decide +kernel

theorem suz_alt : altW 3 suzMod 5 11 6875 625 suzCiSp [] tgtAlt = true := by decide +kernel

end CertificateChecks.KernelAM

end
