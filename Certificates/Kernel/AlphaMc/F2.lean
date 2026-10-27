module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Kernel.AlphaMc.SeedsF2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaCo2Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaCo3Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaCo1RankData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelAM

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
  CFSG.AGLEmbedding.R3

theorem co2_K : mcertN (opsF2K 22) C2A.M C2B.M ⟨AlphaCo2.co2Nregs, AlphaCo2.co2Prog,
    AlphaCo2.co2Mod.modFacts 3 AlphaCo2.co2Tops AlphaCo2.co2Tests⟩ = true := by
  quickRfl

theorem co2_D : (AlphaCo2.co2Mod.wf 3 &&
    pcWf (AlphaCo2.co2Tops ++ AlphaCo2.co2Mod.basisPc 3) &&
    decide (AlphaCo2.co2Tests.length = AlphaCo2.co2Tops.length) &&
    AlphaCo2.co2Tops.all (fun q => AlphaCo2.co2Mod.acts.any (·.reg == q.reg)) &&
    decide (3 ≤ AlphaCo2.co2Mod.basis.length) && AlphaCo2.co2Mod.funOK 3 AlphaCo2.co2Cf &&
    AlphaCo2.co2Mod.altOK 3 AlphaCo2.co2Ci AlphaCo2.co2Ct tgtAlt) = true := by
  decide +kernel

theorem co3_K : mcertN (opsF2K 22) C3A.M C3B.M ⟨AlphaCo3.co3Nregs, AlphaCo3.co3Prog,
    AlphaCo3.co3Mod.modFacts 3 AlphaCo3.co3Tops AlphaCo3.co3Tests⟩ = true := by
  quickRfl

theorem co3_D : (AlphaCo3.co3Mod.wf 3 &&
    pcWf (AlphaCo3.co3Tops ++ AlphaCo3.co3Mod.basisPc 3) &&
    decide (AlphaCo3.co3Tests.length = AlphaCo3.co3Tops.length) &&
    AlphaCo3.co3Tops.all (fun q => AlphaCo3.co3Mod.acts.any (·.reg == q.reg)) &&
    decide (3 ≤ AlphaCo3.co3Mod.basis.length) && AlphaCo3.co3Mod.funOK 3 AlphaCo3.co3Cf &&
    AlphaCo3.co3Mod.altOK 3 AlphaCo3.co3Ci AlphaCo3.co3Ct tgtAlt) = true := by
  have hci : AlphaCo3.co3Ci = fun a₀ b₀ j r s =>
      (((AlphaCo3.co3CiTab.drop ((a₀ * 5 + b₀) * 100)).getD ((j * 5 + r) * 5 + s) 0 : Nat) :
        Int) := by
    funext a₀ b₀ j r s
    rw [AlphaCo3.co3Ci, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
      show (((a₀ * 5 + b₀) * 4 + j) * 5 + r) * 5 + s =
        (a₀ * 5 + b₀) * 100 + ((j * 5 + r) * 5 + s) by omega]
  rw [hci]
  decide +kernel

theorem co1_K : regsN (opsF2K 24) C1A.M C1B.M AlphaCo1Rank.co1rlNregs AlphaCo1Rank.co1rlProg
    (fun R => certN (opsF2K 24) R ⟨AlphaCo1Rank.co1rlNregs, AlphaCo1Rank.co1rlProg,
        AlphaCo1Rank.co1rlSpec.facts⟩ &&
      (opsF2K 24).eq (getN R AlphaCo1Rank.co1rlSpec.rA) C1A.M &&
      (opsF2K 24).eq (getN R AlphaCo1Rank.co1rlSpec.rB) C1B.M) = true := by
  quickRfl

theorem co1_D : (decide (AlphaCo1Rank.co1rlSpec.rA < AlphaCo1Rank.co1rlNregs) &&
    decide (AlphaCo1Rank.co1rlSpec.rB < AlphaCo1Rank.co1rlNregs) &&
    AlphaCo1Rank.co1rlSpec.wf && AlphaCo1Rank.co1rlSpec.linOK AlphaCo1Rank.co1rlTabs) = true := by
  decide +kernel

end CertificateChecks.KernelAM

end
