
module

public import CFSG.GH74.GLS.C3.Layer2.L5C5bInputs
import CFSG.Certificates.Kernel.L5.Fast
import CFSG.Certificates.Kernel.L5.Tables
import CFSG.Certificates.Kernel.L5.Sh0TSound
import CFSG.Certificates.Kernel.L5.HFCIdx
import Certificates.Kernel.L5.Sh0Checks

@[expose] public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open CFSG.Certificates.Kernel
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5065

set_option maxRecDepth 100000

private theorem Sh0L_eq : Sh0L = (List.finRange 16).flatMap fun v =>
    ((d8L.map PkCV.cOf).map PkCV.ev).map fun d => tr16 v * d := by
  rw [PkCV.map_cOf_ev]
  rfl

private theorem sh0_codes : (Sh0L.map pcode).Nodup := by
  rw [Sh0L_eq]
  decide +kernel

private theorem sh0_length : Sh0L.length = 128 := by
  rw [Sh0L_eq]
  decide +kernel

private theorem sh0_mul : mulClosedChkP Sh0L = true := by
  rw [L5S.sh0L_eq, PkCV.mulClosedChkP_map_ev]
  refine L5H.mulClosed_of_tab (n := 128) (mul := L5S.mF) ?_ ?_
  · have h := L5S.sh0L_length
    rwa [L5S.sh0L_eq, List.length_map] at h
  · intro a ha b hb
    obtain ⟨h1, h2⟩ := L5S.mF_spec L5S.sh0Chk_true L5S.sh0C_codes ha hb
    refine ⟨h1, PkCV.ev_injective ?_⟩
    rw [PkCV.ev_mul, ← L5S.sh0L_getD, ← L5S.sh0L_getD, ← L5S.sh0L_getD]
    exact h2

private theorem sh0_inv : invClosedChkP Sh0L = true := by
  rw [← PkCV.map_cOf_ev Sh0L, PkCV.invClosedChkP_map_ev, Sh0L_eq]
  decide +kernel

private theorem mt0Chk_true_0 : mt0Chk = true := KT.mt0Chk_of sh0_codes sh0_mul sh0_length

private theorem inv0Chk_true_1 : inv0Chk = true := KT.inv0Chk_of sh0_codes sh0_inv sh0_length

private theorem one0Chk_true_2 : decide (Sh0L.getD 0 1 = 1) = true := by
  decide +kernel

private theorem idx0Chk_true_3 : idx0Chk = true := by
  unfold idx0Chk idx0
  rw [← PkCV.map_cOf_ev d8L, Sh0L_eq]
  decide +kernel

end CertificateChecks.Batch5065

namespace Certificates

end Certificates
