module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspL33Bridge

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L33

open CFSG.QuasithinUnique.Vol2Native.L239.L33Insp

@[expose] def ncof (x : Nat) : Nat :=
  (dg x 4 * dg x 8 + 2 * (dg x 5 * dg x 7)) % 3 +
  3 * ((2 * (dg x 3 * dg x 8) + dg x 5 * dg x 6) % 3) +
  9 * ((dg x 3 * dg x 7 + 2 * (dg x 4 * dg x 6)) % 3) +
  27 * ((2 * (dg x 1 * dg x 8) + dg x 2 * dg x 7) % 3) +
  81 * ((dg x 0 * dg x 8 + 2 * (dg x 2 * dg x 6)) % 3) +
  243 * ((2 * (dg x 0 * dg x 7) + dg x 1 * dg x 6) % 3) +
  729 * ((dg x 1 * dg x 5 + 2 * (dg x 2 * dg x 4)) % 3) +
  2187 * ((2 * (dg x 0 * dg x 5) + dg x 2 * dg x 3) % 3) +
  6561 * ((dg x 0 * dg x 4 + 2 * (dg x 1 * dg x 3)) % 3)

abbrev Code : Type := Nat × Bool

@[expose] def cmul (a b : Code) : Code :=
  (nmul a.1 (if a.2 then ncof b.1 else b.1), xor a.2 b.2)

@[expose] def cone : Code := (nid, false)

@[expose] def cdelta : Code := (nid, true)

theorem val_sub_mul (a b c d : ZMod 3) :
    (a * b - c * d).val = (a.val * b.val + 2 * (c.val * d.val)) % 3 := by
  revert a b c d
  decide +kernel

theorem val_neg_mul_add (a b c d : ZMod 3) :
    (-(a * b) + c * d).val = (2 * (a.val * b.val) + c.val * d.val) % 3 := by
  revert a b c d
  decide +kernel

theorem rn_inv_transpose (x : S3) : rn ((x⁻¹).transpose) = ncof (rn x) := by
  have d00 : dg (rn x) 0 = (x.1 0 0).val := dg_rn x 0 0
  have d01 : dg (rn x) 1 = (x.1 0 1).val := dg_rn x 0 1
  have d02 : dg (rn x) 2 = (x.1 0 2).val := dg_rn x 0 2
  have d10 : dg (rn x) 3 = (x.1 1 0).val := dg_rn x 1 0
  have d11 : dg (rn x) 4 = (x.1 1 1).val := dg_rn x 1 1
  have d12 : dg (rn x) 5 = (x.1 1 2).val := dg_rn x 1 2
  have d20 : dg (rn x) 6 = (x.1 2 0).val := dg_rn x 2 0
  have d21 : dg (rn x) 7 = (x.1 2 1).val := dg_rn x 2 1
  have d22 : dg (rn x) 8 = (x.1 2 2).val := dg_rn x 2 2
  have a := Matrix.adjugate_fin_three x.1
  have hx : ∀ i j : Fin 3, ((x⁻¹).transpose).1 i j = Matrix.adjugate x.1 j i := fun i j => rfl
  have e00 : (((x⁻¹).transpose).1 0 0).val =
      ((x.1 1 1).val * (x.1 2 2).val + 2 * ((x.1 1 2).val * (x.1 2 1).val)) % 3 := by
    rw [hx, a]
    exact val_sub_mul _ _ _ _
  have e01 : (((x⁻¹).transpose).1 0 1).val =
      (2 * ((x.1 1 0).val * (x.1 2 2).val) + (x.1 1 2).val * (x.1 2 0).val) % 3 := by
    rw [hx, a]
    exact val_neg_mul_add _ _ _ _
  have e02 : (((x⁻¹).transpose).1 0 2).val =
      ((x.1 1 0).val * (x.1 2 1).val + 2 * ((x.1 1 1).val * (x.1 2 0).val)) % 3 := by
    rw [hx, a]
    exact val_sub_mul _ _ _ _
  have e10 : (((x⁻¹).transpose).1 1 0).val =
      (2 * ((x.1 0 1).val * (x.1 2 2).val) + (x.1 0 2).val * (x.1 2 1).val) % 3 := by
    rw [hx, a]
    exact val_neg_mul_add _ _ _ _
  have e11 : (((x⁻¹).transpose).1 1 1).val =
      ((x.1 0 0).val * (x.1 2 2).val + 2 * ((x.1 0 2).val * (x.1 2 0).val)) % 3 := by
    rw [hx, a]
    exact val_sub_mul _ _ _ _
  have e12 : (((x⁻¹).transpose).1 1 2).val =
      (2 * ((x.1 0 0).val * (x.1 2 1).val) + (x.1 0 1).val * (x.1 2 0).val) % 3 := by
    rw [hx, a]
    exact val_neg_mul_add _ _ _ _
  have e20 : (((x⁻¹).transpose).1 2 0).val =
      ((x.1 0 1).val * (x.1 1 2).val + 2 * ((x.1 0 2).val * (x.1 1 1).val)) % 3 := by
    rw [hx, a]
    exact val_sub_mul _ _ _ _
  have e21 : (((x⁻¹).transpose).1 2 1).val =
      (2 * ((x.1 0 0).val * (x.1 1 2).val) + (x.1 0 2).val * (x.1 1 0).val) % 3 := by
    rw [hx, a]
    exact val_neg_mul_add _ _ _ _
  have e22 : (((x⁻¹).transpose).1 2 2).val =
      ((x.1 0 0).val * (x.1 1 1).val + 2 * ((x.1 0 1).val * (x.1 1 0).val)) % 3 := by
    rw [hx, a]
    exact val_sub_mul _ _ _ _
  simp only [ncof, d00, d01, d02, d10, d11, d12, d20, d21, d22]
  simp only [rn, e00, e01, e02, e10, e11, e12, e20, e21, e22]

end CFSG.Quasithin.Vol2.Ch11.SecU1.L33
