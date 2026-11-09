module

public import Certificates.Kernel.B45.C260394Y
public import Certificates.Kernel.B45.C260394YC
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.B45.C260394G

public section

set_option Elab.async false

namespace CertificateChecks.KernelB45.C260394

theorem dblI6_0 : itemB (nat_lit 6) (nat_lit 0) = true := by quickRfl
theorem dblI6_1 : itemB (nat_lit 6) (nat_lit 1) = true := by quickRfl
theorem dblI6_2 : itemB (nat_lit 6) (nat_lit 2) = true := by quickRfl
theorem dblI6_3 : itemB (nat_lit 6) (nat_lit 3) = true := by quickRfl
theorem dblI6_4 : itemB (nat_lit 6) (nat_lit 4) = true := by quickRfl
theorem dblI6_5 : itemB (nat_lit 6) (nat_lit 5) = true := by quickRfl
theorem dblI6_6 : itemB (nat_lit 6) (nat_lit 6) = true := by quickRfl
theorem dblI6_7 : itemB (nat_lit 6) (nat_lit 7) = true := by quickRfl
theorem dblI6_8 : itemB (nat_lit 6) (nat_lit 8) = true := by quickRfl
theorem dblI6_9 : itemB (nat_lit 6) (nat_lit 9) = true := by quickRfl
theorem dblI6_10 : itemB (nat_lit 6) (nat_lit 10) = true := by quickRfl
theorem dblI6_11 : itemB (nat_lit 6) (nat_lit 11) = true := by quickRfl

theorem dblB6 : dblB (nat_lit 6) = true :=
  (dblB_eq_C (nat_lit 6)).trans (dblBC_of (nat_lit 6)
    (all12 (P := fun d => itemB (nat_lit 6) d = true)
      dblI6_0 dblI6_1 dblI6_2 dblI6_3 dblI6_4 dblI6_5 dblI6_6 dblI6_7 dblI6_8 dblI6_9 dblI6_10 dblI6_11))

theorem dblI7_0 : itemB (nat_lit 7) (nat_lit 0) = true := by quickRfl
theorem dblI7_1 : itemB (nat_lit 7) (nat_lit 1) = true := by quickRfl
theorem dblI7_2 : itemB (nat_lit 7) (nat_lit 2) = true := by quickRfl
theorem dblI7_3 : itemB (nat_lit 7) (nat_lit 3) = true := by quickRfl
theorem dblI7_4 : itemB (nat_lit 7) (nat_lit 4) = true := by quickRfl
theorem dblI7_5 : itemB (nat_lit 7) (nat_lit 5) = true := by quickRfl
theorem dblI7_6 : itemB (nat_lit 7) (nat_lit 6) = true := by quickRfl
theorem dblI7_7 : itemB (nat_lit 7) (nat_lit 7) = true := by quickRfl
theorem dblI7_8 : itemB (nat_lit 7) (nat_lit 8) = true := by quickRfl
theorem dblI7_9 : itemB (nat_lit 7) (nat_lit 9) = true := by quickRfl
theorem dblI7_10 : itemB (nat_lit 7) (nat_lit 10) = true := by quickRfl
theorem dblI7_11 : itemB (nat_lit 7) (nat_lit 11) = true := by quickRfl

theorem dblB7 : dblB (nat_lit 7) = true :=
  (dblB_eq_C (nat_lit 7)).trans (dblBC_of (nat_lit 7)
    (all12 (P := fun d => itemB (nat_lit 7) d = true)
      dblI7_0 dblI7_1 dblI7_2 dblI7_3 dblI7_4 dblI7_5 dblI7_6 dblI7_7 dblI7_8 dblI7_9 dblI7_10 dblI7_11))

theorem dblI8_0 : itemB (nat_lit 8) (nat_lit 0) = true := by quickRfl
theorem dblI8_1 : itemB (nat_lit 8) (nat_lit 1) = true := by quickRfl
theorem dblI8_2 : itemB (nat_lit 8) (nat_lit 2) = true := by quickRfl
theorem dblI8_3 : itemB (nat_lit 8) (nat_lit 3) = true := by quickRfl
theorem dblI8_4 : itemB (nat_lit 8) (nat_lit 4) = true := by quickRfl
theorem dblI8_5 : itemB (nat_lit 8) (nat_lit 5) = true := by quickRfl
theorem dblI8_6 : itemB (nat_lit 8) (nat_lit 6) = true := by quickRfl
theorem dblI8_7 : itemB (nat_lit 8) (nat_lit 7) = true := by quickRfl
theorem dblI8_8 : itemB (nat_lit 8) (nat_lit 8) = true := by quickRfl
theorem dblI8_9 : itemB (nat_lit 8) (nat_lit 9) = true := by quickRfl
theorem dblI8_10 : itemB (nat_lit 8) (nat_lit 10) = true := by quickRfl
theorem dblI8_11 : itemB (nat_lit 8) (nat_lit 11) = true := by quickRfl

theorem dblB8 : dblB (nat_lit 8) = true :=
  (dblB_eq_C (nat_lit 8)).trans (dblBC_of (nat_lit 8)
    (all12 (P := fun d => itemB (nat_lit 8) d = true)
      dblI8_0 dblI8_1 dblI8_2 dblI8_3 dblI8_4 dblI8_5 dblI8_6 dblI8_7 dblI8_8 dblI8_9 dblI8_10 dblI8_11))

theorem dblI9_0 : itemB (nat_lit 9) (nat_lit 0) = true := by quickRfl
theorem dblI9_1 : itemB (nat_lit 9) (nat_lit 1) = true := by quickRfl
theorem dblI9_2 : itemB (nat_lit 9) (nat_lit 2) = true := by quickRfl
theorem dblI9_3 : itemB (nat_lit 9) (nat_lit 3) = true := by quickRfl
theorem dblI9_4 : itemB (nat_lit 9) (nat_lit 4) = true := by quickRfl
theorem dblI9_5 : itemB (nat_lit 9) (nat_lit 5) = true := by quickRfl
theorem dblI9_6 : itemB (nat_lit 9) (nat_lit 6) = true := by quickRfl
theorem dblI9_7 : itemB (nat_lit 9) (nat_lit 7) = true := by quickRfl
theorem dblI9_8 : itemB (nat_lit 9) (nat_lit 8) = true := by quickRfl
theorem dblI9_9 : itemB (nat_lit 9) (nat_lit 9) = true := by quickRfl
theorem dblI9_10 : itemB (nat_lit 9) (nat_lit 10) = true := by quickRfl
theorem dblI9_11 : itemB (nat_lit 9) (nat_lit 11) = true := by quickRfl

theorem dblB9 : dblB (nat_lit 9) = true :=
  (dblB_eq_C (nat_lit 9)).trans (dblBC_of (nat_lit 9)
    (all12 (P := fun d => itemB (nat_lit 9) d = true)
      dblI9_0 dblI9_1 dblI9_2 dblI9_3 dblI9_4 dblI9_5 dblI9_6 dblI9_7 dblI9_8 dblI9_9 dblI9_10 dblI9_11))

end CertificateChecks.KernelB45.C260394

end
