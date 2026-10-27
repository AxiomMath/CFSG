module

public import Certificates.Data.Kernel.AlphaGrpK
public import Certificates.Data.Kernel.AlphaFunK
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaFi23Data
public import CFSG.Mathlib.Decide.Nodup
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordDefs

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelAM.Fi23

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.AlphaFi23

theorem w_wf : fi23Mod.wf 3 = true := by decide +kernel

theorem w_pc : pcWf (fi23Tops ++ fi23Mod.basisPc 3) = true := by decide +kernel

theorem w_top : fi23Tops.all (fun q => fi23Mod.acts.any (·.reg == q.reg)) = true := by
  decide +kernel

theorem w_wTops : fi23Tidx.all (fun i => decide (i < fi23Mod.acts.length) &&
    fi23Tops.any (·.reg == (fi23Mod.acts.getD i default).reg)) = true := by
  decide +kernel

@[expose] def wKey (c : Nat) : Nat :=
  [0, 1, 2, 3, 6, 20, 21, 22].foldr (fun d acc => c / 3 ^ d % 3 + 3 * acc) 0

theorem w_wNodup : ((wordsL 3 fi23Mod.basis.length
    (fi23Tidx.map fun i => (fi23Mod.acts.getD i default).mat)).map (codeL 3)).Nodup :=
  CFSG.Decide.nodup_of_bitsetNodup wKey (by decide +kernel)

theorem w_wCount : decide (3 ^ 13 ≤ (wordsL 3 fi23Mod.basis.length
    (fi23Tidx.map fun i => (fi23Mod.acts.getD i default).mat)).length * 3 ^ fi23Mod.basis.length) =
    true := by
  decide +kernel

theorem w_fun : funW 3 fi23Mod 5 10 250 fi23CfSp = true := by decide +kernel

theorem w_alt : altW 3 fi23Mod 5 10 6250 625 fi23CiSp fi23CtSp tgtAlt = true := by
  decide +kernel

end CertificateChecks.KernelAM.Fi23

end
