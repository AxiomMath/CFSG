module

public import Certificates.Data.Kernel.OpsW4C
public import CFSG.RankThree.PartTwo.Census.Sporadic.Fi23W4Data
public import Certificates.Kernel.LocalComp.F3.Fi23
public import Certificates.Kernel.LocalComp.LaySnapsChunksF
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz CFSG.KD.W4Fi23 "Certificates/Kernel/Census/data/w4fi23.json.gz" 22086 15957212289352404548
  (cs : List CFSG.KC.OpsLayK.RChunk)

#lay_snaps_chunks_f CFSG.KD.W4Fi23 3 253 CFSG.KD.LC.F3.Fi23.A CFSG.KD.LC.F3.Fi23.B
  CFSG.KD.W4Fi23.cs

namespace CFSG.KD.W4Fi23

open CFSG.KC.OpsLayK CFSG.KC.OpsW4N CFSG.RankThree.PartTwo.Census CFSG.SectionRank.Native
open CFSG.KD.LC.F3.Fi23 (lay A B)

@[expose] noncomputable def ch (k : Nat) : Bool :=
  chunkV lay (cs.getD k (0, [], [])) (SL.getD k []) (SL.getD (k + 1) [])

#kc_each ch 0 8

theorem pre_K : (progOK fi23W4.base.nregs fi23W4.base.prog &&
    fi23W4.base.outs.all (decide <| · < fi23W4.base.nregs) &&
    decide (fi23W4.inv < fi23W4.base.nregs) && fi23W4.base.tests.all (decide <| · < lay.d)) =
    true := by decide +kernel

theorem ren_K : renOK (fi23W4.base.outs ++ [fi23W4.inv]) fi23W4.base.prog cs = true := by
  decide +kernel

theorem len_K : cs.length = 8 := by decide +kernel

theorem fin_K : w4FinL lay ((SL.getD cs.length []).take fi23W4.base.outs.length)
    (getR lay (SL.getD cs.length []) fi23W4.base.outs.length) fi23W4.base.tests = true := by
  decide +kernel

theorem ren_neg : (!renOK ([1836, 1835, 1841, 1846] ++ [fi23W4.inv]) fi23W4.base.prog cs) =
    true := by decide +kernel

theorem ch_neg : (!chunkV lay (cs.getD 1 (0, [], [])) (SL.getD 2 []) (SL.getD 2 [])) = true := by
  decide +kernel

theorem fin_neg : (!w4FinL lay ((SL.getD 8 []).take 1 ++ (SL.getD 8 []).take 3)
    (getR lay (SL.getD 8 []) 4) fi23W4.base.tests) = true := by decide +kernel

theorem fin_neg_inv : (!w4FinL lay ((SL.getD 8 []).take 4) (getR lay (SL.getD 8 []) 0)
    fi23W4.base.tests) = true := by decide +kernel

end CFSG.KD.W4Fi23

end
