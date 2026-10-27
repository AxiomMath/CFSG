module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyCheck
import Certificates.Kernel.TwoHS.Fy
import Certificates.Kernel.TwoHS.HYGlue

public section

open CFSG.EvenSporadicStandard.TwoHS CFSG.KD.TwoHS

namespace Certificates

theorem fyOK_true : fyOK = true := by
  have e : fyEq = wEq := tblEq_eq_wEq
  have r4 : List.range 4 = [0, 1, 2, 3] := rfl
  have r3 : List.range 3 = [0, 1, 2] := rfl
  unfold fyOK
  rw [e, r4, r3]
  simp only [List.all_cons, List.all_nil, fy_r3, fy_cc0, fy_cc1, fy_cc2, fy_cc3, fy_cr0, fy_cr1,
    fy_cr2, fy_cr3, fy_ca0, fy_ca1, fy_ca2, fy_ca3, fy_b0, fy_b1, fy_b2, fy_c02, fy_c03, fy_c13,
    fy_as, fy_ar, fy_l, fy_r, fy_c01, fy_c20, fy_c2t, Bool.and_self, Bool.not_false,
    Bool.and_true, Nat.zero_add, Nat.reduceAdd]

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26791 : fyOK = true := fyOK_true

end Certificates
