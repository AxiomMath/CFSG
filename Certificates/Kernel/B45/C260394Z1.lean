module

public import Certificates.Kernel.B45.C260394Y
public import Certificates.Kernel.B45.C260394YC
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.B45.C260394G

public section

set_option Elab.async false

namespace CertificateChecks.KernelB45.C260394

theorem dblI3_0 : itemB (nat_lit 3) (nat_lit 0) = true := by quickRfl
theorem dblI3_1 : itemB (nat_lit 3) (nat_lit 1) = true := by quickRfl
theorem dblI3_2 : itemB (nat_lit 3) (nat_lit 2) = true := by quickRfl
theorem dblI3_3 : itemB (nat_lit 3) (nat_lit 3) = true := by quickRfl
theorem dblI3_4 : itemB (nat_lit 3) (nat_lit 4) = true := by quickRfl
theorem dblI3_5 : itemB (nat_lit 3) (nat_lit 5) = true := by quickRfl
theorem dblI3_6 : itemB (nat_lit 3) (nat_lit 6) = true := by quickRfl
theorem dblI3_7 : itemB (nat_lit 3) (nat_lit 7) = true := by quickRfl
theorem dblI3_8 : itemB (nat_lit 3) (nat_lit 8) = true := by quickRfl
theorem dblI3_9 : itemB (nat_lit 3) (nat_lit 9) = true := by quickRfl
theorem dblI3_10 : itemB (nat_lit 3) (nat_lit 10) = true := by quickRfl
theorem dblI3_11 : itemB (nat_lit 3) (nat_lit 11) = true := by quickRfl

theorem dblB3 : dblB (nat_lit 3) = true :=
  (dblB_eq_C (nat_lit 3)).trans (dblBC_of (nat_lit 3)
    (all12 (P := fun d => itemB (nat_lit 3) d = true)
      dblI3_0 dblI3_1 dblI3_2 dblI3_3 dblI3_4 dblI3_5 dblI3_6 dblI3_7 dblI3_8 dblI3_9 dblI3_10 dblI3_11))

theorem dblI4_0 : itemB (nat_lit 4) (nat_lit 0) = true := by quickRfl
theorem dblI4_1 : itemB (nat_lit 4) (nat_lit 1) = true := by quickRfl
theorem dblI4_2 : itemB (nat_lit 4) (nat_lit 2) = true := by quickRfl
theorem dblI4_3 : itemB (nat_lit 4) (nat_lit 3) = true := by quickRfl
theorem dblI4_4 : itemB (nat_lit 4) (nat_lit 4) = true := by quickRfl
theorem dblI4_5 : itemB (nat_lit 4) (nat_lit 5) = true := by quickRfl
theorem dblI4_6 : itemB (nat_lit 4) (nat_lit 6) = true := by quickRfl
theorem dblI4_7 : itemB (nat_lit 4) (nat_lit 7) = true := by quickRfl
theorem dblI4_8 : itemB (nat_lit 4) (nat_lit 8) = true := by quickRfl
theorem dblI4_9 : itemB (nat_lit 4) (nat_lit 9) = true := by quickRfl
theorem dblI4_10 : itemB (nat_lit 4) (nat_lit 10) = true := by quickRfl
theorem dblI4_11 : itemB (nat_lit 4) (nat_lit 11) = true := by quickRfl

theorem dblB4 : dblB (nat_lit 4) = true :=
  (dblB_eq_C (nat_lit 4)).trans (dblBC_of (nat_lit 4)
    (all12 (P := fun d => itemB (nat_lit 4) d = true)
      dblI4_0 dblI4_1 dblI4_2 dblI4_3 dblI4_4 dblI4_5 dblI4_6 dblI4_7 dblI4_8 dblI4_9 dblI4_10 dblI4_11))

theorem dblI5_0 : itemB (nat_lit 5) (nat_lit 0) = true := by quickRfl
theorem dblI5_1 : itemB (nat_lit 5) (nat_lit 1) = true := by quickRfl
theorem dblI5_2 : itemB (nat_lit 5) (nat_lit 2) = true := by quickRfl
theorem dblI5_3 : itemB (nat_lit 5) (nat_lit 3) = true := by quickRfl
theorem dblI5_4 : itemB (nat_lit 5) (nat_lit 4) = true := by quickRfl
theorem dblI5_5 : itemB (nat_lit 5) (nat_lit 5) = true := by quickRfl
theorem dblI5_6 : itemB (nat_lit 5) (nat_lit 6) = true := by quickRfl
theorem dblI5_7 : itemB (nat_lit 5) (nat_lit 7) = true := by quickRfl
theorem dblI5_8 : itemB (nat_lit 5) (nat_lit 8) = true := by quickRfl
theorem dblI5_9 : itemB (nat_lit 5) (nat_lit 9) = true := by quickRfl
theorem dblI5_10 : itemB (nat_lit 5) (nat_lit 10) = true := by quickRfl
theorem dblI5_11 : itemB (nat_lit 5) (nat_lit 11) = true := by quickRfl

theorem dblB5 : dblB (nat_lit 5) = true :=
  (dblB_eq_C (nat_lit 5)).trans (dblBC_of (nat_lit 5)
    (all12 (P := fun d => itemB (nat_lit 5) d = true)
      dblI5_0 dblI5_1 dblI5_2 dblI5_3 dblI5_4 dblI5_5 dblI5_6 dblI5_7 dblI5_8 dblI5_9 dblI5_10 dblI5_11))

end CertificateChecks.KernelB45.C260394

end
