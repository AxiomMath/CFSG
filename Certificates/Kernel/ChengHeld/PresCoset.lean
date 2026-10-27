module

public import CFSG.Certificates.Kernel.CosetW.Columns
public import Certificates.Data.ChengHeldPres

public section

set_option maxRecDepth 400000

open CFSG.CosetTable CFSG.OddStandard.ChengHeldData

namespace CertificateChecks.KernelChengHeld

set_option maxHeartbeats 0 in
theorem e40 : subsetCheckC (relWords4 0) [] 2000 256 = true := by
  rw [subsetCheckC_eq_checkW _ _ (by decide +kernel)]
  decide +kernel

set_option maxHeartbeats 0 in
theorem e41 : subsetCheckC (relWords4 1) [] 2000 256 = true := by
  rw [subsetCheckC_eq_checkW _ _ (by decide +kernel)]
  decide +kernel

set_option maxHeartbeats 0 in
theorem e2 : subsetCheckC relWords2 [] 2000 128 = true := by
  rw [subsetCheckC_eq_checkW _ _ (by decide +kernel)]
  decide +kernel

theorem pres4_true : pres4OK = true := by
  unfold pres4OK
  rw [e40, e41]
  rfl

theorem pres2_true : pres2OK = true := e2

end CertificateChecks.KernelChengHeld

end
