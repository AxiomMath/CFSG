module

public import Certificates.Kernel.Co1B.Chk24510
public import Certificates.Kernel.Co1B.C2044
public import CFSG.Certificates.Kernel.SporSch.Co1HypOneSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.H24510

open CFSG.KS.SporSch.M24 CFSG.EvenSporadicStandard.TwoCo1.HypOne CFSG.Sporadic.Co1Block

open Certificates in
theorem c24510 : CFSG.EvenSporadicStandard.TwoCo1.HypOne.perfectCheckA = true := by
  unfold perfectCheckA
  exact perfectCheckOf_of_K C2044.bray_eq
    (fun i hi => Nat.eq_of_beq_eq_true (MatL.allN_iff.1 kPb i hi)) kP kpi
    (fun l hl => Nat.eq_of_beq_eq_true (MatL.allN_iff.1 kUb l hl)) kU kci
    (fun j hj => Nat.eq_of_beq_eq_true (MatL.allN_iff.1 kFb j hj)) kF kfi rfl
    (fun l hl => Nat.eq_of_beq_eq_true (MatL.allN_iff.1 kf l hl))
    (fun l hl => Nat.eq_of_beq_eq_true (MatL.allN_iff.1 kQb l hl)) kQ kqi
    (by rw [C2044.qRows_len]; rfl)
    (fun l hl => by
      have hl8 : l < 8 := by simpa [perfQIdxA] using hl
      rw [C2044.qRows_get hl8, Nat.eq_of_beq_eq_true (MatL.allN_iff.1 kq l hl)]
      rfl)

end CertificateChecks.KernelCo1B.H24510

end
