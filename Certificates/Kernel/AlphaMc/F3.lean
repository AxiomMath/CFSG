module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Kernel.LocalComp.LaySeeds
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaONData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaMcLData
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelAM.ON 3 154
  CFSG.Blueprint.NativeSporadic.ONSeed1 CFSG.Blueprint.NativeSporadic.ONSeed2

#lay_seeds CertificateChecks.KernelAM.McL 3 21
  CFSG.Blueprint.NativeSporadic.McLSeed1 CFSG.Blueprint.NativeSporadic.McLSeed2

public section

set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelAM

open CFSG.KC.OpsLayK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.AGLEmbedding.R3

theorem on_K : mcertL ON.lay ON.A ON.B ⟨AlphaON.onNregs, AlphaON.onProg,
    AlphaON.onMod.facts 3⟩ = true := by
  quickRfl

theorem on_D : (AlphaON.onMod.wf 3 && decide (AlphaON.onMod.basis.length ≤ 4) &&
    decide (0 < AlphaON.onMod.basis.length) && decide (1 < AlphaON.onMod.basis.length) &&
    AlphaON.onMod.funOK 3 AlphaON.onCf &&
    AlphaON.onMod.altOK 3 AlphaON.onCi AlphaON.onCt
      (tgtNondeg AlphaON.onMod.basis.length AlphaON.onQ 0 1)) = true := by
  decide +kernel

theorem mcl_K : mcertL McL.lay McL.A McL.B ⟨AlphaMcL.mclNregs, AlphaMcL.mclProg,
    AlphaMcL.mclMod.modFacts 3 AlphaMcL.mclTops AlphaMcL.mclTests⟩ = true := by
  quickRfl

theorem mcl_D : (AlphaMcL.mclMod.wf 3 &&
    pcWf (AlphaMcL.mclTops ++ AlphaMcL.mclMod.basisPc 3) &&
    decide (AlphaMcL.mclTests.length = AlphaMcL.mclTops.length) &&
    AlphaMcL.mclTops.all (fun q => AlphaMcL.mclMod.acts.any (·.reg == q.reg)) &&
    decide (3 ≤ AlphaMcL.mclMod.basis.length) && AlphaMcL.mclMod.funOK 3 AlphaMcL.mclCf &&
    AlphaMcL.mclMod.altOK 3 AlphaMcL.mclCi AlphaMcL.mclCt tgtAlt) = true := by
  decide +kernel

theorem f3_neg : (!mcertL ON.lay ON.A ON.B ⟨2, [], [.ord 0 1]⟩) = true ∧
    (!mcertL McL.lay McL.A McL.B ⟨2, [], [.eq [(0, 1)] [(1, 1)]]⟩) = true := by
  constructor <;> quickRfl

end CertificateChecks.KernelAM

end
