module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaCo1RankData
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.AlphaMc.F2
import CFSG.Certificates.Kernel.OpsMcertNSound
import CFSG.Certificates.Kernel.OpsKSound

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
  CFSG.Blueprint

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaCo1Rank
  CFSG.Blueprint.NativeSporadic in
theorem certificate9603 : rlCheck (ops2 24) Co1Seed1 Co1Seed2 co1rlNregs co1rlProg co1rlSpec
    co1rlTabs = true := by
  have hA : (ops2 24).decode NativeSporadic.Co1Seed1 = (hom2 24 (by norm_num)).U KernelAM.C1A.M := by
    rw [KernelAM.C1A.eq]
    exact CFSG.KC.Co1F2.bind_sound KernelAM.C1A.bind
  have hB : (ops2 24).decode NativeSporadic.Co1Seed2 = (hom2 24 (by norm_num)).U KernelAM.C1B.M := by
    rw [KernelAM.C1B.eq]
    exact CFSG.KC.Co1F2.bind_sound KernelAM.C1B.bind
  have hD := KernelAM.co1_D
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hD
  obtain ⟨⟨⟨hrA, hrB⟩, hwf⟩, hlin⟩ := hD
  obtain ⟨hm, h0, h1⟩ := seeds_of_N (hom2 24 (by norm_num)) hA hB trivial trivial hrA hrB
    KernelAM.co1_K
  unfold rlCheck
  rw [hm, h0, h1, hwf, hlin]
  simp [hrA, hrB]

end Certificates
