module

public import CFSG.Quasithin.Background.HL42DataInputs

public section

namespace CertificateChecks.KernelDirect.C7026

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L4
open scoped Matrix

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem blk4_mul_0 :
    ∀ X Y : Fin 2 → Fin 2 → ZMod 2,
      (1 + blk4 X) * (1 + blk4 Y) = 1 + blk4 (X + Y) := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem blk4_inj_1 :
    ∀ X Y : Fin 2 → Fin 2 → ZMod 2, 1 + blk4 X = 1 + blk4 Y → X = Y := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem blk5_mul_2 :
    ∀ X Y : Fin 3 → Fin 2 → ZMod 2,
      (1 + blk5 X) * (1 + blk5 Y) = 1 + blk5 (X + Y) := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem blk5_inj_3 :
    ∀ X Y : Fin 3 → Fin 2 → ZMod 2, 1 + blk5 X = 1 + blk5 Y → X = Y := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem card_fix_blk4_4 :
    (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      ∀ X : Fin 2 → Fin 2 → ZMod 2, (1 + blk4 X) *ᵥ v = v).card = 4 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem card_fix_blk4_transpose_5 :
    (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      ∀ X : Fin 2 → Fin 2 → ZMod 2, (1 + blk4 X)ᵀ *ᵥ v = v).card = 4 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem card_fix_blk5_6 :
    (Finset.univ.filter fun v : Fin 5 → ZMod 2 =>
      ∀ X : Fin 3 → Fin 2 → ZMod 2, (1 + blk5 X) *ᵥ v = v).card = 8 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem single_mul_self_7 :
    ∀ i j : Fin 4, i ≠ j →
      (1 + Matrix.single i j (1 : ZMod 2)) * (1 + Matrix.single i j 1) = 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem single_mulVec_e0_8 :
    ∀ i j : Fin 4, j ≠ 0 →
      (1 + Matrix.single i j (1 : ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem single_transpose_9 :
    ∀ i j : Fin 4,
      (1 + Matrix.single i j (1 : ZMod 2))ᵀ = 1 + Matrix.single j i 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem eq_zero_of_fix_single_10 :
    ∀ w : Fin 4 → ZMod 2,
      (∀ i j : Fin 4, j ≠ 0 → i ≠ j → (1 + Matrix.single j i (1 : ZMod 2)) *ᵥ w = w) → w = 0 := by
  decide +kernel

end CertificateChecks.KernelDirect.C7026
