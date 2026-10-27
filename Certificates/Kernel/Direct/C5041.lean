module

public import CFSG.GH74.GLS.C3.Layer2.FinModelTabInputs

public section

namespace CertificateChecks.KernelDirect.C5041

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.C3 CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.Model
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem validB6_0 : (mkTab 6).validB = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem validB7_1 : (mkTab 7).validB = true := by
  decide +kernel

end CertificateChecks.KernelDirect.C5041
