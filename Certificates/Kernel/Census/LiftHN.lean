module

public import Certificates.Data.Kernel.OpsV4
public import Certificates.Data.TripleCoverLift.HN
public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Kernel.LocalComp.LaySnapsChunks
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelCensus.LiftHN.L 5 133
  CFSG.Blueprint.NativeSporadic.HNSeed1 CFSG.Blueprint.NativeSporadic.HNSeed2

#kc_repo #kc_json_gz CertificateChecks.KernelCensus.LiftHN
  "Certificates/Kernel/Census/data/lifthn.json.gz" 19051 17683689881706239441
  (cs : List CFSG.KC.OpsLayK.RChunk)

#lay_snaps_chunks CertificateChecks.KernelCensus.LiftHN 5 133
  CertificateChecks.KernelCensus.LiftHN.L.A CertificateChecks.KernelCensus.LiftHN.L.B
  CertificateChecks.KernelCensus.LiftHN.cs

public section

namespace CertificateChecks.KernelCensus.LiftHN

open CFSG.KC.OpsLayK CFSG.KC.OpsV4 CFSG.RankThree.PartTwo.Sec4.Census CFSG.SectionRank.Native

@[expose] noncomputable def ch (k : Nat) : Bool :=
  chunkV L.lay (cs.getD k (0, [], [])) (SL.getD k []) (SL.getD (k + 1) [])

#kc_each CertificateChecks.KernelCensus.LiftHN.ch 0 6

theorem pre_K : liftPreL L.lay hnLift = true := by decide +kernel

theorem ren_K : renOK (regsL hnLift) hnLift.base.prog cs = true := by decide +kernel

theorem len_K : cs.length = 6 := by decide +kernel

theorem fin_K : liftFinL L.lay (SL.getD cs.length []) hnLift = true := by decide +kernel

theorem ren_neg : (!renOK [911, 901, 912, 434, 881, 1010, 1239, 1272, 1501] hnLift.base.prog cs) =
    true := by decide +kernel

theorem ch_neg : (!chunkV L.lay (cs.getD 1 (0, [], [])) (SL.getD 2 []) (SL.getD 2 [])) = true := by
  decide +kernel

theorem fin_neg_rep : (!liftFinL L.lay (SL.getD 6 [])
    { hnLift with base := { hnLift.base with outs := [901, 901, 912] } }) = true := by
  decide +kernel

theorem fin_neg_inv : (!liftFinL L.lay (SL.getD 6 []) { hnLift with inv₁ := 901 }) = true := by
  decide +kernel

theorem fin_neg_rel : (!liftFinL L.lay (SL.getD 6 []) { hnLift with rels := [.fix 1010 0] }) =
    true := by
  decide +kernel

theorem fin_neg_unit : (!liftFinL L.lay (SL.getD 6 [])
    { hnLift with units := [(1010, 1), (1239, 6), (1272, 6), (1501, 6)] }) = true := by
  decide +kernel

end CertificateChecks.KernelCensus.LiftHN

end
