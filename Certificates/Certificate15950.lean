module

public import CFSG.Timmesfeld.Exceptional.DeepThreeNearCertificate15950Inputs
public import CFSG.Timmesfeld.Moufang.J2

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Timmesfeld CFSG.Timmesfeld.Moufang CFSG.Certificates CFSG.Blueprint
open CFSG.Sporadic.Bridge.J2 (idL lwordL)
open CFSG.Timmesfeld.Moufang.J2 (genL nativeGens genL_wf unitGen_val unitGen_inv
  coe_signedProd_nativeGens signedProd_comp)

private theorem cert15950_0 : ∀ k : Fin 3, lwordL genL genL
    (((List.replicate 4 (wJ 0 k)).flatten).map fun l => (l.1.val, l.2)) idL = idL := by
  decide +kernel

private theorem cert15950_1 : ∀ k : Fin 3, lwordL genL genL
    (((List.replicate 4 (wJ 1 k)).flatten).map fun l => (l.1.val, l.2)) idL = idL := by
  decide +kernel

private theorem cert15950_2 : ∀ k : Fin 3, lwordL genL genL
    (((List.replicate 4 (wJ 2 k)).flatten).map fun l => (l.1.val, l.2)) idL = idL := by
  decide +kernel

private theorem cert15950_3 : ∀ k : Fin 3, lwordL genL genL
    (((List.replicate 4 (wJ 3 k)).flatten).map fun l => (l.1.val, l.2)) idL = idL := by
  decide +kernel

end CFSG.Timmesfeld.Moufang.Deep

namespace Certificates

open CFSG.Timmesfeld.Moufang.Deep in
open CFSG.Sporadic.Bridge.J2 (idL lwordL) in
open CFSG.Timmesfeld.Moufang.J2 (genL) in
theorem certificate15950 : (
    ∀ k : Fin 3, lwordL genL genL
        (((List.replicate 4 (wJ 0 k)).flatten).map fun l => (l.1.val, l.2)) idL = idL
  ) ∧ (
    ∀ k : Fin 3, lwordL genL genL
        (((List.replicate 4 (wJ 1 k)).flatten).map fun l => (l.1.val, l.2)) idL = idL
  ) ∧ (
    ∀ k : Fin 3, lwordL genL genL
        (((List.replicate 4 (wJ 2 k)).flatten).map fun l => (l.1.val, l.2)) idL = idL
  ) ∧ (
    ∀ k : Fin 3, lwordL genL genL
        (((List.replicate 4 (wJ 3 k)).flatten).map fun l => (l.1.val, l.2)) idL = idL
  ) := by
  exact ⟨CFSG.Timmesfeld.Moufang.Deep.cert15950_0, CFSG.Timmesfeld.Moufang.Deep.cert15950_1,
    CFSG.Timmesfeld.Moufang.Deep.cert15950_2, CFSG.Timmesfeld.Moufang.Deep.cert15950_3⟩

end Certificates
