module

public import CFSG.Quasithin.Background.ShultG53Layers
public import CFSG.Quasithin.Background.ShultG53CoverData

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix
  CFSG.Quasithin.H13.A6 CFSG.Quasithin.RonanG51 Equiv

@[expose] def inLine : Fin 2 → V4 → Prop
  | 0 => fun y => y = 0 ∨ y = ![1, 0, 0, 0] ∨ y = ![0, 0, 1, 0] ∨ y = ![1, 0, 1, 0]
  | 1 => fun y => y = 0 ∨ y = ![1, 0, 0, 0] ∨ y = ![0, 0, 1, 1] ∨ y = ![1, 0, 1, 1]

instance (k : Fin 2) (y : V4) : Decidable (inLine k y) :=
  match k with
  | 0 => inferInstanceAs (Decidable
      (y = 0 ∨ y = ![1, 0, 0, 0] ∨ y = ![0, 0, 1, 0] ∨ y = ![1, 0, 1, 0]))
  | 1 => inferInstanceAs (Decidable
      (y = 0 ∨ y = ![1, 0, 0, 0] ∨ y = ![0, 0, 1, 1] ∨ y = ![1, 0, 1, 1]))

@[expose] def y2 : Fin 2 → V4
  | 0 => ![1, 0, 0, 0]
  | 1 => ![0, 0, 1, 1]

@[expose] def y3 : Fin 2 → V4
  | 0 => ![0, 0, 1, 0]
  | 1 => ![1, 0, 1, 1]

@[expose] def lineSharp (k : Fin 2) : Fn := fun w =>
  if w = x0 k ∨ w = y2 k ∨ w = y3 k then 1 else 0

@[expose] def delta (a : V4) : Fn := fun w => if w = a then 1 else 0

@[expose] def onesOm : Fn := fun w => if w = 0 then 0 else 1

@[expose] def ymap : Fin 15 → V4 := ![
  ![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![0, 0, 1, 0], ![1, 0, 1, 0], ![0, 1, 1, 0],
  ![1, 1, 1, 0], ![0, 0, 0, 1], ![1, 0, 0, 1], ![0, 1, 0, 1], ![1, 1, 0, 1], ![0, 0, 1, 1],
  ![1, 0, 1, 1], ![0, 1, 1, 1], ![1, 1, 1, 1]]

@[expose] def RS0 : Fin 2 → Fin 15 → Perm (Fin 6) := ![RS0_0, RS0_1]

@[expose] def RS2 : Fin 2 → Fin 5 → Perm (Fin 6) := ![RS2_0, RS2_1]

theorem inLine_iff : ∀ (k : Fin 2) (y : V4),
    inLine k y ↔ y = 0 ∨ y = x0 k ∨ y = y2 k ∨ y = y3 k := by
  decide +kernel

theorem points_aux : ∀ k : Fin 2, x0 k ≠ 0 ∧ y2 k ≠ 0 ∧ y3 k ≠ 0 ∧ x0 k ≠ y2 k ∧ x0 k ≠ y3 k ∧
    y2 k ≠ y3 k ∧ x0 k + y2 k + y3 k = 0 := by
  decide +kernel

theorem h0_sign : ∀ k : Fin 2, Perm.sign (h0P k) = 1 := by decide +kernel

theorem h0_cycle : ∀ k : Fin 2, Matrix.mulVec (Rm k (h0P k)) (x0 k) = y2 k ∧
    Matrix.mulVec (Rm k (h0P k)) (y2 k) = y3 k ∧ Matrix.mulVec (Rm k (h0P k)) (y3 k) = x0 k := by
  decide +kernel

theorem h0_line : ∀ (k : Fin 2) (y : V4),
    inLine k y → inLine k (Matrix.mulVec (Rm k (h0P k)) y) := by
  decide +kernel

theorem lineSharp_eq : ∀ (k : Fin 2) (w : V4), lineSharp k w =
    (delta (x0 k) + delta (y2 k) + delta (y3 k) : Fn) w := by
  decide +kernel

theorem U2gen_eq : ∀ (k : Fin 2) (w : V4), U2gen k w = (lineSharp k + onesOm) w := by
  decide +kernel

theorem U0gen_eq : ∀ (k : Fin 2) (w : V4), U0gen k w = (onesOm + delta (x0 k) : Fn) w := by
  decide +kernel

theorem RS2_sign : ∀ (k : Fin 2) (i : Fin 5), Perm.sign (RS2 k i) = 1 := by decide +kernel

theorem spread_sum : ∀ (k : Fin 2) (w : V4),
    ∑ i : Fin 5, lineSharp k (Matrix.mulVec (Rm k (RS2 k i)⁻¹) w) = onesOm w := by
  decide +kernel

theorem ymap_cover : ∀ y : V4, y ≠ 0 → ∃ i : Fin 15, ymap i = y := by decide +kernel

theorem RS0_act : ∀ (k : Fin 2) (i : Fin 15), Perm.sign (RS0 k i) = 1 ∧
    Matrix.mulVec (Rm k (RS0 k i)) (x0 k) = ymap i := by
  decide +kernel

theorem L3_ok : ∀ (k : Fin 2) (a : Fin 9), Perm.sign (L3P k a) = 1 ∧
    Matrix.mulVec (Rm k (L3P k a)) (x0 k) = x0 k ∧ ∀ i, L3P k a (L3P k a (L3P k a i)) = i := by
  decide +kernel

theorem t_ok : ∀ k : Fin 2, Perm.sign (tP k) = 1 ∧ Matrix.mulVec (Rm k (tP k)) (x0 k) = x0 k ∧
    (∀ i, tP k (tP k i) = i) ∧
    Matrix.mulVec (Rm k (tP k)) (y0P k) + y0P k = x0 k := by
  decide +kernel

theorem SP_decomp : ∀ (k : Fin 2) (j : Fin 24), ∃ a b : Fin 9,
    (∀ i, SP k j i = L3P k a (L3P k b i)) ∨ (∀ i, SP k j i = tP k (L3P k a (L3P k b i))) := by
  decide +kernel

theorem SP_inj : ∀ (k : Fin 2) (j j' : Fin 24), (∀ i, SP k j i = SP k j' i) → j = j' := by
  decide +kernel

theorem SP_sign : ∀ (k : Fin 2) (j : Fin 24), Perm.sign (SP k j) = 1 := by decide +kernel

end CFSG.Quasithin.ShultG53
