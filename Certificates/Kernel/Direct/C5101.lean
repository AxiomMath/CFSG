module

public import CFSG.GH74.GLS.Stage4.Q9.PermCharInputs
import CFSG.GH74.GLS.Stage4.Q9.ModelBaseInputs
import CFSG.GH74.GLS.Stage4.Q9.ModelBase

public section

namespace CertificateChecks.KernelDirect.C5101

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Q9

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem card_Lg : Fintype.card Lg = 1440 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem card_filter_BL : (Finset.univ.filter fun l : Lg => l ∈ BL).card = 144 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem repPt_spec : ∀ x : Lg,
    (Finset.univ.filter fun p : Option F9 => (repPt p)⁻¹ * x ∈ BL).card = 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sum_sq_aTabFast : ∑ l : Lg, aTabFast l ^ 2 = 1440 := by
  decide +kernel

end CertificateChecks.KernelDirect.C5101
