module

public import Certificates.Kernel.B45.C260394Y
public import Certificates.Kernel.B45.C260394YC
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.B45.C260394G

public section

set_option Elab.async false

namespace CertificateChecks.KernelB45.C260394

theorem dblI0_0 : itemB (nat_lit 0) (nat_lit 0) = true := by quickRfl
theorem dblI0_1 : itemB (nat_lit 0) (nat_lit 1) = true := by quickRfl
theorem dblI0_2 : itemB (nat_lit 0) (nat_lit 2) = true := by quickRfl
theorem dblI0_3 : itemB (nat_lit 0) (nat_lit 3) = true := by quickRfl
theorem dblI0_4 : itemB (nat_lit 0) (nat_lit 4) = true := by quickRfl
theorem dblI0_5 : itemB (nat_lit 0) (nat_lit 5) = true := by quickRfl
theorem dblI0_6 : itemB (nat_lit 0) (nat_lit 6) = true := by quickRfl
theorem dblI0_7 : itemB (nat_lit 0) (nat_lit 7) = true := by quickRfl
theorem dblI0_8 : itemB (nat_lit 0) (nat_lit 8) = true := by quickRfl
theorem dblI0_9 : itemB (nat_lit 0) (nat_lit 9) = true := by quickRfl
theorem dblI0_10 : itemB (nat_lit 0) (nat_lit 10) = true := by quickRfl
theorem dblI0_11 : itemB (nat_lit 0) (nat_lit 11) = true := by quickRfl

theorem dblB0 : dblB (nat_lit 0) = true :=
  (dblB_eq_C (nat_lit 0)).trans (dblBC_of (nat_lit 0)
    (all12 (P := fun d => itemB (nat_lit 0) d = true)
      dblI0_0 dblI0_1 dblI0_2 dblI0_3 dblI0_4 dblI0_5 dblI0_6 dblI0_7 dblI0_8 dblI0_9 dblI0_10 dblI0_11))

theorem dblI1_0 : itemB (nat_lit 1) (nat_lit 0) = true := by quickRfl
theorem dblI1_1 : itemB (nat_lit 1) (nat_lit 1) = true := by quickRfl
theorem dblI1_2 : itemB (nat_lit 1) (nat_lit 2) = true := by quickRfl
theorem dblI1_3 : itemB (nat_lit 1) (nat_lit 3) = true := by quickRfl
theorem dblI1_4 : itemB (nat_lit 1) (nat_lit 4) = true := by quickRfl
theorem dblI1_5 : itemB (nat_lit 1) (nat_lit 5) = true := by quickRfl
theorem dblI1_6 : itemB (nat_lit 1) (nat_lit 6) = true := by quickRfl
theorem dblI1_7 : itemB (nat_lit 1) (nat_lit 7) = true := by quickRfl
theorem dblI1_8 : itemB (nat_lit 1) (nat_lit 8) = true := by quickRfl
theorem dblI1_9 : itemB (nat_lit 1) (nat_lit 9) = true := by quickRfl
theorem dblI1_10 : itemB (nat_lit 1) (nat_lit 10) = true := by quickRfl
theorem dblI1_11 : itemB (nat_lit 1) (nat_lit 11) = true := by quickRfl

theorem dblB1 : dblB (nat_lit 1) = true :=
  (dblB_eq_C (nat_lit 1)).trans (dblBC_of (nat_lit 1)
    (all12 (P := fun d => itemB (nat_lit 1) d = true)
      dblI1_0 dblI1_1 dblI1_2 dblI1_3 dblI1_4 dblI1_5 dblI1_6 dblI1_7 dblI1_8 dblI1_9 dblI1_10 dblI1_11))

theorem dblI2_0 : itemB (nat_lit 2) (nat_lit 0) = true := by quickRfl
theorem dblI2_1 : itemB (nat_lit 2) (nat_lit 1) = true := by quickRfl
theorem dblI2_2 : itemB (nat_lit 2) (nat_lit 2) = true := by quickRfl
theorem dblI2_3 : itemB (nat_lit 2) (nat_lit 3) = true := by quickRfl
theorem dblI2_4 : itemB (nat_lit 2) (nat_lit 4) = true := by quickRfl
theorem dblI2_5 : itemB (nat_lit 2) (nat_lit 5) = true := by quickRfl
theorem dblI2_6 : itemB (nat_lit 2) (nat_lit 6) = true := by quickRfl
theorem dblI2_7 : itemB (nat_lit 2) (nat_lit 7) = true := by quickRfl
theorem dblI2_8 : itemB (nat_lit 2) (nat_lit 8) = true := by quickRfl
theorem dblI2_9 : itemB (nat_lit 2) (nat_lit 9) = true := by quickRfl
theorem dblI2_10 : itemB (nat_lit 2) (nat_lit 10) = true := by quickRfl
theorem dblI2_11 : itemB (nat_lit 2) (nat_lit 11) = true := by quickRfl

theorem dblB2 : dblB (nat_lit 2) = true :=
  (dblB_eq_C (nat_lit 2)).trans (dblBC_of (nat_lit 2)
    (all12 (P := fun d => itemB (nat_lit 2) d = true)
      dblI2_0 dblI2_1 dblI2_2 dblI2_3 dblI2_4 dblI2_5 dblI2_6 dblI2_7 dblI2_8 dblI2_9 dblI2_10 dblI2_11))

end CertificateChecks.KernelB45.C260394

end
