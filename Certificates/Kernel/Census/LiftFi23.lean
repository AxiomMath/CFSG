module

public import Certificates.Data.Kernel.OpsV4
public import Certificates.Data.Fi23Lift
public import Certificates.Kernel.LocalComp.F3.Fi23
public import Certificates.Kernel.LocalComp.LaySnapsChunksF
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelCensus.LiftFi23
  "Certificates/Kernel/Census/data/liftfi23.json.gz" 16045 249258710014154195
  (cs : List CFSG.KC.OpsLayK.RChunk)

#lay_snaps_chunks_f CertificateChecks.KernelCensus.LiftFi23 3 253
  CFSG.KD.LC.F3.Fi23.A CFSG.KD.LC.F3.Fi23.B CertificateChecks.KernelCensus.LiftFi23.cs

public section

namespace CertificateChecks.KernelCensus.LiftFi23

open CFSG.KC.OpsLayK CFSG.KC.OpsV4 CFSG.SectionRank.Native

@[expose] noncomputable def ch431003_ (k : Nat) : Bool :=
  chunkV CFSG.KD.LC.F3.Fi23.lay (cs.getD k (0, [], [])) (SL.getD k []) (SL.getD (k + 1) [])

#kc_each CertificateChecks.KernelCensus.LiftFi23.ch431003_ 0 10

theorem pre_K : liftPreL CFSG.KD.LC.F3.Fi23.lay fi23Lift = true := by quickRfl

theorem ren_K : renOK (regsL fi23Lift) fi23Lift.base.prog cs = true := by quickRfl

theorem len_K : cs.length = 10 := by decide +kernel

theorem fin_K : liftFinL CFSG.KD.LC.F3.Fi23.lay (SL.getD cs.length []) fi23Lift = true := by
  quickRfl

end CertificateChecks.KernelCensus.LiftFi23

end
