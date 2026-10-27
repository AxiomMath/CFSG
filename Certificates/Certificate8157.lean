module

public import CFSG.RankThree.PartTwo.Census.Sporadic.Fi23W4Data
import CFSG.Certificates.Kernel.OpsW4NSound
import CFSG.Certificates.Kernel.OpsW4CSound
import Certificates.Kernel.Census.W4Fi23
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate1012Base
public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Census CFSG.KD.LC.F3 CFSG.KD.W4Fi23

private theorem w4Fi23_ch_all : ∀ i < cs.length, CFSG.KC.OpsLayK.chunkV Fi23.lay (cs.getD i (0, [], []))
    (SL.getD i []) (SL.getD (i + 1) []) = true := by
  intro i hi
  rw [len_K] at hi
  interval_cases i
  exacts [ch0, ch1, ch2, ch3, ch4, ch5, ch6, ch7]

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Census CFSG.Blueprint
  CFSG.SectionRank CFSG.SectionRank.Native in
theorem certificate8157 : W4Data.check (ops3 253) fi23W4 = true :=
  CFSG.KC.OpsW4N.w4Check_of_L Fi23.lay_ok rfl rfl Fi23.decA Fi23.decB
    ((rfl : fi23W4.base.seedA = CFSG.Blueprint.NativeSporadic.Fi23Seed1).trans Fi23.LA_eq)
    ((rfl : fi23W4.base.seedB = CFSG.Blueprint.NativeSporadic.Fi23Seed2).trans Fi23.LB_eq)
    (CFSG.KC.OpsW4N.w4L_of_chunks (S := fun i => SL.getD i []) pre_K ren_K rfl w4Fi23_ch_all fin_K)

end Certificates

end
