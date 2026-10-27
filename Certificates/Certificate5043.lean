module

public import CFSG.GH74.GLS.C3.Layer2.L4ModelE2
import Certificates.Kernel.GH74Tab.E23Glue

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
theorem certificate5043 : ((mkTab 6).claimG (mkTab 6).e2P1 = true)
    ∧ ((mkTab 7).claimG (mkTab 7).e2P1 = true)
    ∧ ((mkTab 6).claimG (mkTab 6).e2P2 = true)
    ∧ ((mkTab 7).claimG (mkTab 7).e2P2 = true)
    ∧ ((mkTab 6).claimG (mkTab 6).e2P3 = true)
    ∧ ((mkTab 7).claimG (mkTab 7).e2P3 = true)
    ∧ ((mkTab 6).claimG (mkTab 6).e2P4 = true)
    ∧ ((mkTab 7).claimG (mkTab 7).e2P4 = true) :=
  ⟨c5043_e2P1_6, c5043_e2P1_7, c5043_e2P2_6, c5043_e2P2_7, c5043_e2P3_6, c5043_e2P3_7,
    c5043_e2P4_6, c5043_e2P4_7⟩

end Certificates
