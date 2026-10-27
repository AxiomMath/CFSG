module

public import Certificates.Data.RankThree46Odd.HN
public import Certificates.Data.CFSGNative.SectionRank.Fp
import CFSG.Certificates.Kernel.OpsV4Sound
import Certificates.Kernel.Census.V4HN
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Census CFSG.KD.V4HN
open CFSG.KD.LC.Fp.HN (lay lay_ok decA decB LA_eq LB_eq)

private theorem v4HN_ch_all : ∀ i < cs.length, CFSG.KC.OpsLayK.chunkV lay (cs.getD i (0, [], []))
    (SL.getD i []) (SL.getD (i + 1) []) = true := by
  intro i hi
  rw [len_K] at hi
  interval_cases i
  exacts [ch0, ch1, ch2, ch3]

open CFSG.RankThree.PartTwo.Census CFSG.SectionRank.Native in
theorem certificate8091 : V4Data.check (opsP 5 133) hnV4 = true :=
  CFSG.KC.OpsV4.v4Check_of_chunksP (S := fun i => SL.getD i []) lay_ok rfl rfl decA decB
    ((rfl : hnV4.base.seedA = CFSG.Blueprint.NativeSporadic.HNSeed1).trans LA_eq)
    ((rfl : hnV4.base.seedB = CFSG.Blueprint.NativeSporadic.HNSeed2).trans LB_eq)
    pre_K ren_K rfl v4HN_ch_all fin_K

end Certificates

end
