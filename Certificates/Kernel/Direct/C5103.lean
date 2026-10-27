module

public import CFSG.GH74.GLS.Stage4.Q9.ThetaModel
public import CFSG.GH74.GLS.Stage4.Q9.FrobCount
public import CFSG.GH74.GLS.Stage4.Q9.ThetaPropsInputs
import CFSG.GH74.GLS.Stage4.Q9.ModelBase
import CFSG.GH74.GLS.Stage4.Q9.ChatOrders
import CFSG.GH74.GLS.Stage4.Q9.Tables

public section

namespace CertificateChecks.KernelDirect.C5103

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Q9
open CFSG.GH74.GLS.Stage4.Q9.ThetaProps
open CFSG Subgroup

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem typ_memList_0 : ∀ l : Lg, typ l ∈ typList := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem typCountsOK_eq_1 : typCountsOK = true := by
  decide +kernel

end CertificateChecks.KernelDirect.C5103
