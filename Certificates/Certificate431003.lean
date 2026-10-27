module

public import Certificates.Data.Fi23Lift
import CFSG.Certificates.Kernel.OpsV4Sound
import Certificates.Kernel.Census.LiftFi23
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Open.LocalVocabulary
public import Certificates.Data.CFSGNative.SectionRank.F3

public section

namespace CertificateChecks.Batch431003

open CFSG.SectionRank.Native CFSG.KC.OpsLayK CFSG.KC.OpsV4 CertificateChecks.KernelCensus
  CFSG.KD.LC.F3

private theorem fi23_ch : ∀ i < LiftFi23.cs.length, chunkV Fi23.lay
    (LiftFi23.cs.getD i (0, [], [])) (LiftFi23.SL.getD i []) (LiftFi23.SL.getD (i + 1) []) =
      true := by
  intro i hi
  rw [LiftFi23.len_K] at hi
  interval_cases i
  exacts [LiftFi23.ch431003_0, LiftFi23.ch431003_1, LiftFi23.ch431003_2, LiftFi23.ch431003_3,
    LiftFi23.ch431003_4, LiftFi23.ch431003_5, LiftFi23.ch431003_6, LiftFi23.ch431003_7,
    LiftFi23.ch431003_8, LiftFi23.ch431003_9]

private theorem fi23 : LiftData.check (ops3 253) fi23Lift = true :=
  liftCheck_of_chunks (S := fun i => LiftFi23.SL.getD i []) Fi23.lay_ok rfl rfl Fi23.decA Fi23.decB
    ((rfl : fi23Lift.base.seedA = CFSG.Blueprint.NativeSporadic.Fi23Seed1).trans Fi23.LA_eq)
    ((rfl : fi23Lift.base.seedB = CFSG.Blueprint.NativeSporadic.Fi23Seed2).trans Fi23.LB_eq)
    LiftFi23.pre_K LiftFi23.ren_K rfl fi23_ch LiftFi23.fin_K

end CertificateChecks.Batch431003

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native in
theorem certificate431003 : LiftData.check (ops3 253) fi23Lift = true := CertificateChecks.Batch431003.fi23

end Certificates
