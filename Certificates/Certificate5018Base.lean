
module

public import CFSG.GH74.E2.SD16CertInputs
public import CFSG.GH74.E2.AutCert
import all CFSG.GH74.E2.AutCert
public import CFSG.CharacterTheory.Semidihedral.NormalForm
import all CFSG.CharacterTheory.Semidihedral.NormalForm
import all CFSG.CharacterTheory.Semidihedral.Model
import all CFSG.GH74.E2.SD16CertInputs
import all CFSG.GH74.E2.SD16CertBase

@[expose] public section

open CFSG
open CFSG.GH74
open CFSG.GH74.E2
open CFSG.Semidihedral

namespace CertificateChecks.Batch5018

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem sd16_two_involutions_0 : ∃ x y : SD16M, x * x = 1 ∧ y * y = 1 ∧ x ≠ 1 ∧ y ≠ 1 ∧
    x * y = y * x ∧ x ≠ y := by
  refine ⟨(gx 4).1 ^ 4, (gy 4).1, ?_⟩
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem relA_Q8_1 : RelA (gx 2) (gy 2) := by
  unfold RelA gx gy
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem relB_Q8_2 : RelB 2 (gx 2) (gy 2) (gc 2) := by
  unfold RelB gx gy gc
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem relC_Q8_3 : RelC 2 (gx 2) (gy 2) (gc 2) (gd 2) := by
  unfold RelC gx gy gc gd
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem searchOK_Q8_4 : SearchOK 2 (gc 2 ^ 2) := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem relA_Q16_5 : RelA (gx 4) (gy 4) := by
  unfold RelA gx gy
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem relB_Q16_6 : RelB 4 (gx 4) (gy 4) (gc 4) := by
  unfold RelB gx gy gc
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem relC_Q16_7 : RelC 4 (gx 4) (gy 4) (gc 4) (gd 4) := by
  unfold RelC gx gy gc gd
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem searchOK_Q16_8 : SearchOK 4 (gc 4 ^ 4) := by
  decide +kernel

end CertificateChecks.Batch5018

namespace Certificates

end Certificates
