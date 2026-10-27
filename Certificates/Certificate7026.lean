module

public import CFSG.Quasithin.Background.HL42DataInputs
import Certificates.Kernel.Direct.C7026

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelDirect.C7026 in
open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L4 in
open scoped Matrix in
theorem certificate7026 :
    (∀ X Y : Fin 2 → Fin 2 → ZMod 2,
       (1 + blk4 X) * (1 + blk4 Y) = 1 + blk4 (X + Y))
    ∧ (∀ X Y : Fin 2 → Fin 2 → ZMod 2, 1 + blk4 X = 1 + blk4 Y → X = Y)
    ∧ (∀ X Y : Fin 3 → Fin 2 → ZMod 2,
       (1 + blk5 X) * (1 + blk5 Y) = 1 + blk5 (X + Y))
    ∧ (∀ X Y : Fin 3 → Fin 2 → ZMod 2, 1 + blk5 X = 1 + blk5 Y → X = Y)
    ∧ ((Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
       ∀ X : Fin 2 → Fin 2 → ZMod 2, (1 + blk4 X) *ᵥ v = v).card = 4)
    ∧ ((Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
       ∀ X : Fin 2 → Fin 2 → ZMod 2, (1 + blk4 X)ᵀ *ᵥ v = v).card = 4)
    ∧ ((Finset.univ.filter fun v : Fin 5 → ZMod 2 =>
       ∀ X : Fin 3 → Fin 2 → ZMod 2, (1 + blk5 X) *ᵥ v = v).card = 8)
    ∧ (∀ i j : Fin 4, i ≠ j →
       (1 + Matrix.single i j (1 : ZMod 2)) * (1 + Matrix.single i j 1) = 1)
    ∧ (∀ i j : Fin 4, j ≠ 0 →
       (1 + Matrix.single i j (1 : ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1)
    ∧ (∀ i j : Fin 4,
       (1 + Matrix.single i j (1 : ZMod 2))ᵀ = 1 + Matrix.single j i 1)
    ∧ (∀ w : Fin 4 → ZMod 2,
       (∀ i j : Fin 4, j ≠ 0 → i ≠ j → (1 + Matrix.single j i (1 : ZMod 2)) *ᵥ w = w) → w = 0) :=
  ⟨blk4_mul_0, blk4_inj_1, blk5_mul_2, blk5_inj_3, card_fix_blk4_4, card_fix_blk4_transpose_5,
    card_fix_blk5_6, single_mul_self_7, single_mulVec_e0_8, single_transpose_9,
    eq_zero_of_fix_single_10⟩

end Certificates
