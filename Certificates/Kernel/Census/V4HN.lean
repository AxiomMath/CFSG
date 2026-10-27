module

public import Certificates.Data.Kernel.OpsV4
public import Certificates.Data.Kernel.OpsRenL
public import Certificates.Data.RankThree46Odd.HN
public import Certificates.Kernel.LocalComp.Fp.HN
public import Certificates.Kernel.LocalComp.LaySnapsChunks
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz CFSG.KD.V4HN "Certificates/Kernel/Census/data/v4hn.json.gz" 11580 11126438805012824855
  (cs : List CFSG.KC.OpsLayK.RChunk)

#lay_snaps_chunks CFSG.KD.V4HN 5 133 CFSG.KD.LC.Fp.HN.A CFSG.KD.LC.Fp.HN.B CFSG.KD.V4HN.cs

namespace CFSG.KD.V4HN

open CFSG.KC.OpsLayK CFSG.KC.OpsV4 CFSG.RankThree.PartTwo.Census CFSG.SectionRank.Native
open CFSG.KD.LC.Fp.HN (lay A B)

@[expose] noncomputable def ch (k : Nat) : Bool :=
  chunkV lay (cs.getD k (0, [], [])) (SL.getD k []) (SL.getD (k + 1) [])

#kc_each CFSG.KD.V4HN.ch 0 4

theorem pre_K : liftPreL lay (v4Lift hnV4.base hnV4.inv₁ hnV4.inv₂) = true := by decide +kernel

theorem ren_K : renOK (regsL (v4Lift hnV4.base hnV4.inv₁ hnV4.inv₂)) hnV4.base.prog cs = true := by
  decide +kernel

theorem len_K : cs.length = 4 := by decide +kernel

theorem fin_K : v4FinL lay (SL.getD cs.length []) hnV4.base hnV4.inv₁ hnV4.inv₂ = true := by
  decide +kernel

theorem ren_neg : (!renOK [901, 880, 911, 434, 881] hnV4.base.prog cs) = true := by decide +kernel

theorem ch_neg : (!chunkV lay (cs.getD 1 (0, [], [])) (SL.getD 2 []) (SL.getD 2 [])) = true := by
  decide +kernel

theorem fin_neg : (!v4FinL lay (SL.getD 4 []) { hnV4.base with outs := [880, 880, 911] } 434 881) =
    true := by decide +kernel

theorem fin_neg_inv : (!v4FinL lay (SL.getD 4 []) hnV4.base 880 881) = true := by decide +kernel

end CFSG.KD.V4HN

end
