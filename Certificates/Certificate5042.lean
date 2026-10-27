module

public import CFSG.GH74.GLS.C3.Layer2.L4ModelE1
import Certificates.Kernel.GH74Tab.E1Glue
import Certificates.Kernel.GH74Tab.CfGlue

public section

namespace Certificates

open CFSG.KD.GH74Tab

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.Model in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2 in
theorem certificate5042 : ((mkTab 6).claimG (mkTab 6).e1P1 = true)
    ∧ ((mkTab 7).claimG (mkTab 7).e1P1 = true)
    ∧ ((mkTab 6).claimG (mkTab 6).e1P2 = true)
    ∧ ((mkTab 7).claimG (mkTab 7).e1P2 = true)
    ∧ ((mkTab 6).claimG (mkTab 6).e1P3 = true)
    ∧ ((mkTab 7).claimG (mkTab 7).e1P3 = true)
    ∧ ((mkTab 6).cfCoverE1 = true)
    ∧ ((mkTab 7).cfCoverE1 = true)
    ∧ ((cfSetE1 6).card = 64)
    ∧ ((cfSetE1 7).card = 192) :=
  ⟨c5042_e1P1_6, c5042_e1P1_7, c5042_e1P2_6, c5042_e1P2_7, c5042_e1P3_6, c5042_e1P3_7,
    c5042_cfCoverE1_6, c5042_cfCoverE1_7, c5042_cfSetE1_6, c5042_cfSetE1_7⟩

end Certificates
