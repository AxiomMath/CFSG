module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMGenData
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SectionRank.F2
import Certificates.Kernel.FongSporM.MGen
import Certificates.Kernel.TcGen.F2Glue

public section

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.Blueprint
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal CertificateChecks.KernelTc
  CertificateChecks.KernelMGen

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal CFSG.SectionRank.Native CFSG.Blueprint in
theorem certificate40261 : MGen.check (ops2 80) NativeSporadic.J3Seed1 NativeSporadic.J3Seed2 j3_5_claims = true ∧
    MGen.check (ops2 22) NativeSporadic.Co3Seed1 NativeSporadic.Co3Seed2 co3_7_claims = true ∧
    MGen.check (ops2 22) NativeSporadic.Co2Seed1 NativeSporadic.Co2Seed2 co2_7_claims = true := by
  have hD := ch40261_wf
  simp only [Bool.and_eq_true] at hD
  obtain ⟨⟨hj, h3⟩, h2⟩ := hD
  have jA : (ops2 80).decode NativeSporadic.J3Seed1 =
      (hom2 80 (by norm_num)).U KernelJ3L.JA.M := by
    rw [KernelJ3L.JA.eq]
    exact CFSG.KC.Co1F2.bind_sound KernelJ3L.JA.bind
  have jB : (ops2 80).decode NativeSporadic.J3Seed2 =
      (hom2 80 (by norm_num)).U KernelJ3L.JB.M := by
    rw [KernelJ3L.JB.eq]
    exact CFSG.KC.Co1F2.bind_sound KernelJ3L.JB.bind
  refine ⟨?_, ?_, ?_⟩
  · rw [MGen.check, hj, Bool.true_and]
    exact mcertCheck_of_N (hom2 80 (by norm_num)) jA jB trivial trivial ch40261_j3
  · rw [MGen.check, h3, Bool.true_and]
    exact mcertCheck_of_N (hom2 22 (by norm_num)) c3A c3B trivial trivial ch40261_co3
  · rw [MGen.check, h2, Bool.true_and]
    exact mcertCheck_of_N (hom2 22 (by norm_num)) c2A c2B trivial trivial ch40261_co2

end Certificates
