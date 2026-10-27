module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl3
import Certificates.Kernel.TwoHS.WInv
import Certificates.Kernel.TwoHS.HYGlue

public section

open CFSG.EvenSporadicStandard.TwoHS CFSG.KD.TwoHS CFSG.KS.MulH

namespace Certificates

theorem harWInvOK_true : harWInvOK = true := by
  obtain ⟨ea, ca⟩ := tU_eq (wd := [1]) (by decide)
  obtain ⟨eb, cb⟩ := tU_eq (wd := [2, 3, 3]) (by decide)
  unfold harWInvOK
  rw [ea, eb, idT_eq, compT_unpack ca ca, compT_unpack cb cb,
    tblEq_unpack (CFSG.KC.BfsPin.canonK_pcomp ca ca) cId, tblEq_unpack ca cId,
    tblEq_unpack (CFSG.KC.BfsPin.canonK_pcomp cb cb) cId, tblEq_unpack cb cId]
  exact winv_ok

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26134 : harWInvOK = true := harWInvOK_true

end Certificates
