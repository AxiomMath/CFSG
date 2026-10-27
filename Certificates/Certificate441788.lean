module

public import Certificates.Data.FzL410Model
import CFSG.Certificates.Kernel.FzL410M.Sound
import Certificates.Kernel.FzL410M.Checks
import Mathlib.Tactic.IntervalCases

public section

namespace Certificates

open Certificates.FzL410.KM CFSG.FzL410KM CertificateChecks.FzL410KM

theorem certificate441788 : FzL410.ModelFacts := by
  have h64 : (64 : ℕ) < 512 := by decide
  have hcs : Certificates.FzL410.CardS := @cardS act_ok 64 128 h64 tM_eq.symm rfl cardS_ok
  refine modelFacts act_ok ord_ok colR_disj colP_disj ?_ ?_ sqz_ok
    (rQ act_ok rq_0 rq_1 rq_2 rq_3 rq_4) qc_ok ef_ok centP_ok invF_ok ?_ hcs
    (sLem act_ok _ _ sl_ok)
  · refine slices 16 32 fun i hi => ?_
    interval_cases i
    · exact charS_iff.1 charR_0
    · exact charS_iff.1 charR_1
    · exact charS_iff.1 charR_2
    · exact charS_iff.1 charR_3
    · exact charS_iff.1 charR_4
    · exact charS_iff.1 charR_5
    · exact charS_iff.1 charR_6
    · exact charS_iff.1 charR_7
    · exact charS_iff.1 charR_8
    · exact charS_iff.1 charR_9
    · exact charS_iff.1 charR_10
    · exact charS_iff.1 charR_11
    · exact charS_iff.1 charR_12
    · exact charS_iff.1 charR_13
    · exact charS_iff.1 charR_14
    · exact charS_iff.1 charR_15
  · refine slices 8 32 fun i hi => ?_
    interval_cases i
    · exact charS_iff.1 charP_0
    · exact charS_iff.1 charP_1
    · exact charS_iff.1 charP_2
    · exact charS_iff.1 charP_3
    · exact charS_iff.1 charP_4
    · exact charS_iff.1 charP_5
    · exact charS_iff.1 charP_6
    · exact charS_iff.1 charP_7
  · refine fusAll act_ok ⟨_, fus_t⟩ fun j hj => ?_
    interval_cases j
    · exact ⟨_, fus_0⟩
    · exact ⟨_, fus_1⟩
    · exact ⟨_, fus_2⟩
    · exact ⟨_, fus_3⟩
    · exact ⟨_, fus_4⟩
    · exact ⟨_, fus_5⟩
    · exact ⟨_, fus_6⟩
    · exact ⟨_, fus_7⟩
    · exact ⟨_, fus_8⟩
    · exact ⟨_, fus_9⟩
    · exact ⟨_, fus_10⟩
    · exact ⟨_, fus_11⟩
    · exact ⟨_, fus_12⟩
    · exact ⟨_, fus_13⟩
    · exact ⟨_, fus_14⟩
    · exact ⟨_, fus_15⟩

end Certificates
