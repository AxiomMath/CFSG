module

public import CFSG.CGT.L5R.L52EnumInputs
import CFSG.Certificates.Kernel.CosetW.Columns

public section

set_option maxRecDepth 400000

open CFSG.CGT.L5R CFSG.CosetTable

namespace Certificates

set_option maxHeartbeats 0 in
open CFSG.CGT.L5R in
theorem certificate21195 : l52Enum = true := by
  unfold l52Enum
  rw [subsetCheckC_eq_checkW _ _ (by decide +kernel)]
  decide +kernel

end Certificates
