module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0TypEighthInputs
import CFSG.Certificates.Kernel.EvenSporCo0.EighthSound
import Certificates.Kernel.EvenSporCo0.Checks

public section

open CFSG.EvenSporadicStandard.TwoCo1 CFSG.KC.EvenSporCo0 CFSG.Monster.B.TwoA.Census

namespace CertificateChecks.Batch24532

open CFSG.EvenSporadicStandard.TwoCo1 CFSG.KC.EvenSporCo0 CFSG.Monster.B.TwoA.Census

open CertificateChecks.KernelCo0

private theorem blk_all : ∀ j < 16, blk j = true
  | 0, _ => blk0 | 1, _ => blk1 | 2, _ => blk2 | 3, _ => blk3 | 4, _ => blk4 | 5, _ => blk5
  | 6, _ => blk6 | 7, _ => blk7 | 8, _ => blk8 | 9, _ => blk9 | 10, _ => blk10 | 11, _ => blk11
  | 12, _ => blk12 | 13, _ => blk13 | 14, _ => blk14 | 15, _ => blk15
  | _ + 16, h => absurd h (by omega)

private theorem pts_all : ∀ i < S.N, eighthOKP (S.T i) = true := by
  intro i hi
  rw [N_eq] at hi
  have hb := blk_all (i / 64) (by omega)
  unfold blk eighthBlk at hb
  have h := List.all_eq_true.1 hb (i % 64) (List.mem_range.2 (Nat.mod_lt _ (by norm_num)))
  rwa [Nat.div_add_mod] at h

theorem eighthCheck_true : eighthCheck = true := by
  have hg := gensK_true
  unfold gensK at hg
  rw [Bool.and_eq_true] at hg
  refine eighthCheck_of (Nat.eq_of_beq_eq_true hg.1) (fun k hk => ?_) S.ok edgesOK replayOK'
    (by rw [N_eq]; norm_num) (by rw [N_eq]; norm_num) pts_all
  exact beq_iff_eq.1 (List.all_eq_true.1 hg.2 k (List.mem_range.2 hk))

end CertificateChecks.Batch24532

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoCo1 in
theorem certificate24532 : eighthCheck = true := CertificateChecks.Batch24532.eighthCheck_true

end Certificates
