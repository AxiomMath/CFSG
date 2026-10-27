module

public import Certificates.Data.Kernel.OpsV4
public import Certificates.Data.TripleCoverLift.Ly
public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Kernel.LocalComp.LaySnapsChunks
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelCensus.LiftLy.L 5 111
  CFSG.Blueprint.NativeSporadic.LySeed1 CFSG.Blueprint.NativeSporadic.LySeed2

#kc_repo #kc_json_gz CertificateChecks.KernelCensus.LiftLy
  "Certificates/Kernel/Census/data/liftly.json.gz" 12517 14247238191966524620
  (cs : List CFSG.KC.OpsLayK.RChunk)

#lay_snaps_chunks CertificateChecks.KernelCensus.LiftLy 5 111
  CertificateChecks.KernelCensus.LiftLy.L.A CertificateChecks.KernelCensus.LiftLy.L.B
  CertificateChecks.KernelCensus.LiftLy.cs

public section

namespace CertificateChecks.KernelCensus.LiftLy

open CFSG.KC.OpsLayK CFSG.KC.OpsV4 CFSG.RankThree.PartTwo.Sec4.Census CFSG.SectionRank.Native

@[expose] noncomputable def ch (k : Nat) : Bool :=
  chunkV L.lay (cs.getD k (0, [], [])) (SL.getD k []) (SL.getD (k + 1) [])

#kc_each ch 0 5

theorem pre_K : liftPreL L.lay lyLift = true := by decide +kernel

theorem ren_K : renOK (regsL lyLift) lyLift.base.prog cs = true := by decide +kernel

theorem len_K : cs.length = 5 := by decide +kernel

theorem fin_K : liftFinL L.lay (SL.getD cs.length []) lyLift = true := by decide +kernel

theorem ren_neg : (!renOK [490, 478, 500, 22, 22, 779, 925, 1070] lyLift.base.prog cs) = true := by
  decide +kernel

theorem ch_neg : (!chunkV L.lay (cs.getD 1 (0, [], [])) (SL.getD 2 []) (SL.getD 2 [])) = true := by
  decide +kernel

theorem fin_neg_rep : (!liftFinL L.lay (SL.getD 5 [])
    { lyLift with base := { lyLift.base with outs := [478, 478, 500] } }) = true := by
  decide +kernel

theorem fin_neg_inv : (!liftFinL L.lay (SL.getD 5 []) { lyLift with inv₁ := 478 }) = true := by
  decide +kernel

theorem fin_neg_rel : (!liftFinL L.lay (SL.getD 5 []) { lyLift with rels := [.fix 779 0] }) =
    true := by
  decide +kernel

theorem fin_neg_unit : (!liftFinL L.lay (SL.getD 5 [])
    { lyLift with units := [(779, 1), (925, 24), (1070, 12)] }) = true := by
  decide +kernel

end CertificateChecks.KernelCensus.LiftLy

end
