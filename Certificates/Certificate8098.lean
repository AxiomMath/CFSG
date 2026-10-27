module

public import Certificates.Data.TripleCoverLift.Ly
public import Certificates.Data.TripleCoverLift.HN
public import Certificates.Data.CFSGNative.SectionRank.Fp
import CFSG.Certificates.Kernel.OpsV4Sound
import Certificates.Kernel.Census.LiftHN
import Certificates.Kernel.Census.LiftLy
import all CFSG.Blueprint.NativeSporadic

public section

namespace CertificateChecks.Batch8098

open CFSG.RankThree.PartTwo.Sec4.Census CFSG.SectionRank.Native CFSG.KC.OpsLayK CFSG.KC.OpsV4
  CertificateChecks.KernelCensus

private theorem ly_ch : ∀ i < LiftLy.cs.length, chunkV LiftLy.L.lay
    (LiftLy.cs.getD i (0, [], [])) (LiftLy.SL.getD i []) (LiftLy.SL.getD (i + 1) []) = true := by
  intro i hi
  rw [LiftLy.len_K] at hi
  interval_cases i
  exacts [LiftLy.ch0, LiftLy.ch1, LiftLy.ch2, LiftLy.ch3, LiftLy.ch4]

private theorem hn_ch : ∀ i < LiftHN.cs.length, chunkV LiftHN.L.lay
    (LiftHN.cs.getD i (0, [], [])) (LiftHN.SL.getD i []) (LiftHN.SL.getD (i + 1) []) = true := by
  intro i hi
  rw [LiftHN.len_K] at hi
  interval_cases i
  exacts [LiftHN.ch0, LiftHN.ch1, LiftHN.ch2, LiftHN.ch3, LiftHN.ch4, LiftHN.ch5]

private theorem ly : LiftData.check (opsP 5 111) lyLift = true :=
  liftCheck_of_chunksP (S := fun i => LiftLy.SL.getD i []) LiftLy.L.lay_ok rfl rfl LiftLy.L.decA
    LiftLy.L.decB
    ((rfl : lyLift.base.seedA = CFSG.Blueprint.NativeSporadic.LySeed1).trans LiftLy.L.LA_eq)
    ((rfl : lyLift.base.seedB = CFSG.Blueprint.NativeSporadic.LySeed2).trans LiftLy.L.LB_eq)
    LiftLy.pre_K LiftLy.ren_K rfl ly_ch LiftLy.fin_K

private theorem hn : LiftData.check (opsP 5 133) hnLift = true :=
  liftCheck_of_chunksP (S := fun i => LiftHN.SL.getD i []) LiftHN.L.lay_ok rfl rfl LiftHN.L.decA
    LiftHN.L.decB
    ((rfl : hnLift.base.seedA = CFSG.Blueprint.NativeSporadic.HNSeed1).trans LiftHN.L.LA_eq)
    ((rfl : hnLift.base.seedB = CFSG.Blueprint.NativeSporadic.HNSeed2).trans LiftHN.L.LB_eq)
    LiftHN.pre_K LiftHN.ren_K rfl hn_ch LiftHN.fin_K

end CertificateChecks.Batch8098

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Census CFSG.SectionRank.Native in
theorem certificate8098 : LiftData.check (opsP 5 111) lyLift = true ∧ LiftData.check (opsP 5 133) hnLift = true := ⟨CertificateChecks.Batch8098.ly, CertificateChecks.Batch8098.hn⟩

end Certificates
