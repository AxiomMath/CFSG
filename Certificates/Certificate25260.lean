module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelGenInputs
import Certificates.Kernel.Fi23C.Final

namespace CertificateChecks.Batch25260

open CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen CertificateChecks.KernelFi23C

theorem frame_ok : (List.range 22).all (fun j =>
    E (ΦI (genU.getD j 0)) == CFSG.EvenSporadicStandard.TwoFi22.FrameJ.fjPts.getD (j + 1) 0) =
      true := by
  decide +kernel

theorem genU_lt : (List.range 22).all (fun j => decide (genU.getD j 0 < 3510)) = true := by
  decide +kernel

theorem genCertA_ok : genCertA = true := by
  unfold genCertA genChecksA
  rw [CFSG.KD.Fi23K.orbitData_eq']
  refine List.all_eq_true.2 fun j hj => ?_
  have hu := of_decide_eq_true (List.all_eq_true.1 genU_lt j hj)
  rw [starPhiPos_get hu, starPts_get dTable_star (phi_facts hu).2.1]
  exact List.all_eq_true.1 frame_ok j hj

end CertificateChecks.Batch25260

public section

namespace Certificates

open CertificateChecks

theorem certificate25260 : CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen.genCertA = true := CertificateChecks.Batch25260.genCertA_ok

end Certificates
