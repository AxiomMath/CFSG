module

public import CFSG.Quasithin.Background.B4Models
public meta import Mathlib.Algebra.Field.ZMod
public meta import Mathlib.Data.Matrix.Mul
public meta import Mathlib.Data.Fin.VecNotation
public import CFSG.Quasithin.Background.HL42DataInputs
public import Certificates.Certificate7026

public section

namespace CFSG.Quasithin

namespace H

namespace L4

open scoped Matrix

theorem blk4_mul : ∀ X Y : Fin 2 → Fin 2 → ZMod 2,
    (1 + blk4 X) * (1 + blk4 Y) = 1 + blk4 (X + Y) :=
  Certificates.certificate7026.1

theorem blk4_inj :
    ∀ X Y : Fin 2 → Fin 2 → ZMod 2, 1 + blk4 X = 1 + blk4 Y → X = Y :=
  Certificates.certificate7026.2.1

theorem blk5_mul : ∀ X Y : Fin 3 → Fin 2 → ZMod 2,
    (1 + blk5 X) * (1 + blk5 Y) = 1 + blk5 (X + Y) :=
  Certificates.certificate7026.2.2.1

theorem blk5_inj :
    ∀ X Y : Fin 3 → Fin 2 → ZMod 2, 1 + blk5 X = 1 + blk5 Y → X = Y :=
  Certificates.certificate7026.2.2.2.1

theorem card_fix_blk4 :
    (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      ∀ X : Fin 2 → Fin 2 → ZMod 2, (1 + blk4 X) *ᵥ v = v).card = 4 :=
  Certificates.certificate7026.2.2.2.2.1

theorem card_fix_blk4_transpose :
    (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      ∀ X : Fin 2 → Fin 2 → ZMod 2, (1 + blk4 X)ᵀ *ᵥ v = v).card = 4 :=
  Certificates.certificate7026.2.2.2.2.2.1

theorem card_fix_blk5 :
    (Finset.univ.filter fun v : Fin 5 → ZMod 2 =>
      ∀ X : Fin 3 → Fin 2 → ZMod 2, (1 + blk5 X) *ᵥ v = v).card = 8 :=
  Certificates.certificate7026.2.2.2.2.2.2.1

theorem single_mul_self : ∀ i j : Fin 4, i ≠ j →
    (1 + Matrix.single i j (1 : ZMod 2)) * (1 + Matrix.single i j 1) = 1 :=
  Certificates.certificate7026.2.2.2.2.2.2.2.1

theorem single_mulVec_e0 : ∀ i j : Fin 4, j ≠ 0 →
    (1 + Matrix.single i j (1 : ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1 :=
  Certificates.certificate7026.2.2.2.2.2.2.2.2.1

theorem single_transpose : ∀ i j : Fin 4,
    (1 + Matrix.single i j (1 : ZMod 2))ᵀ = 1 + Matrix.single j i 1 :=
  Certificates.certificate7026.2.2.2.2.2.2.2.2.2.1

theorem eq_zero_of_fix_single : ∀ w : Fin 4 → ZMod 2,
    (∀ i j : Fin 4, j ≠ 0 → i ≠ j → (1 + Matrix.single j i (1 : ZMod 2)) *ᵥ w = w) → w = 0 :=
  Certificates.certificate7026.2.2.2.2.2.2.2.2.2.2

end L4

end H

end CFSG.Quasithin
