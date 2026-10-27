module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUModCheck
import Certificates.Kernel.TwoHS.Mz
import Certificates.Kernel.TwoHS.HYGlue

public section

open CFSG.EvenSporadicStandard.TwoHS CFSG.KD.TwoHS

namespace Certificates

theorem mzOK_true : mzOK = true := by
  have e : mzEq = wEq := tblEq_eq_wEq
  have r3 : List.range 3 = [0, 1, 2] := rfl
  unfold mzOK
  rw [e, r3]
  simp only [List.all_cons, List.all_nil, mz_r3, mz_rb0, mz_rb1, mz_rb2, mz_as, mz_ab0, mz_ab1,
    mz_ab2, mz_ra, mz_p3, mz_pr, mz_pa, mz_g1, mz_g2, mz_r, mz_p, mz_pR, mz_prr, Bool.and_self,
    Bool.not_false, Bool.and_true]

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26824 : mzOK = true := mzOK_true

end Certificates
