module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.ThreeGroupSmallExponent
open MulAction

theorem cube_smul
    {H Y : Type*} [Group H] [MulAction H Y] [Finite Y]
    (hH : IsPGroup 3 H) (hY : Nat.card Y < 9) (h : H) (y : Y) : h ^ 3 • y = y := by
  classical
  let _ : Fintype Y := Fintype.ofFinite Y
  let _ : Fintype (orbit (Subgroup.zpowers h) y) := Fintype.ofFinite _
  obtain ⟨e,he⟩ := (hH.to_subgroup (Subgroup.zpowers h)).card_orbit y
  have hb := Nat.card_le_card_of_injective (fun z : orbit (Subgroup.zpowers h) y => z.val)
    Subtype.val_injective
  have he1 : e ≤ 1 := by
    by_contra hn
    have hp : 9 ≤ 3 ^ e := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 2 ≤ e)
    rw [he] at hb
    omega
  apply pow_smul_eq_iff_minimalPeriod_dvd.mpr
  rw [minimalPeriod_eq_card,← Nat.card_eq_fintype_card,he]
  interval_cases e <;> norm_num

end FiveTransitive.ThreeGroupSmallExponent

end CFSG
