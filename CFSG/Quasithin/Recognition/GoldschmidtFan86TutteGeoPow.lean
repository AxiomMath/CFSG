module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteGeoShift
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteSys

public section

namespace CFSG.Quasithin.Fan86.Tutte.Geo

open CFSG.Quasithin.F6.GoldAmL3T CFSG.Quasithin.Fan86.Tutte.Red

variable {W : Type} {Γ : SimpleGraph W} {H : Type} [Group H] [MulAction H W] {s : ℕ}

structure Config (a : Arc Γ s) (r l ξ : H) : Prop where
  r_shift : ∀ j, j < s → r • a.vert j = a.vert (j + 1)
  l_shift : ∀ j, j < s → l • a.vert j = a.vert (j + 1)
  ne : r ≠ l
  cases : ∀ g : H, (∀ j, j < s → g • a.vert j = a.vert (j + 1)) → g = r ∨ g = l
  xi_vert : ∀ j, j ≤ s → ξ • a.vert j = a.vert (s - j)
  xi_sq : ξ * ξ = 1

theorem pow_smul_vert {a : Arc Γ s} {g : H} (hg : ∀ j, j < s → g • a.vert j = a.vert (j + 1)) :
    ∀ k j, j + k ≤ s → (g ^ k) • a.vert j = a.vert (j + k)
  | 0, j, _ => by simp
  | k + 1, j, h => by
    rw [pow_succ', mul_smul, pow_smul_vert hg k j (by omega), hg (j + k) (by omega)]
    rfl

theorem inv_pow_smul_vert {a : Arc Γ s} {g : H} (hg : ∀ j, j < s → g • a.vert j = a.vert (j + 1))
    {k j : ℕ} (h : j + k ≤ s) : (g ^ k)⁻¹ • a.vert (j + k) = a.vert j := by
  rw [inv_smul_eq_iff, pow_smul_vert hg k j h]

theorem tx_natCast (r l : H) (i : ℕ) : tx r l (i : ℤ) = (l ^ i)⁻¹ * r ^ i := by
  simp [tx, zpow_neg, zpow_natCast]

namespace RegData

variable (R : RegData Γ H s) {a : Arc Γ s} {r l ξ : H}

include R

theorem shift_last_ne (C : Config a r l ξ) : r • a.vert s ≠ l • a.vert s := by
  intro h
  refine C.ne (R.eq_of_agree a fun j hj => ?_)
  rcases Nat.lt_or_ge j s with hjs | hjs
  · rw [C.r_shift j hjs, C.l_shift j hjs]
  · have : j = s := by omega
    rw [this]
    exact h

omit R in
theorem tx_smul_vert (C : Config a r l ξ) {i j : ℕ} (hi : i ≤ s) (hj : j ≤ s - i) :
    tx r l (i : ℤ) • a.vert j = a.vert j := by
  rw [tx_natCast, mul_smul, pow_smul_vert C.r_shift i j (by omega),
    inv_pow_smul_vert C.l_shift (k := i) (j := j) (by omega)]

theorem tx_smul_vert_ne (C : Config a r l ξ) {i : ℕ} (hi1 : 1 ≤ i) (his : i ≤ s) :
    tx r l (i : ℤ) • a.vert (s - i + 1) ≠ a.vert (s - i + 1) := by
  intro h
  have hr : r ^ i • a.vert (s - i + 1) = r • a.vert s := by
    obtain ⟨t, rfl⟩ : ∃ t, i = t + 1 := ⟨i - 1, by omega⟩
    rw [pow_succ', mul_smul, pow_smul_vert C.r_shift t (s - (t + 1) + 1) (by omega),
      show s - (t + 1) + 1 + t = s by omega]
  have hl : l ^ i • a.vert (s - i + 1) = l • a.vert s := by
    obtain ⟨t, rfl⟩ : ∃ t, i = t + 1 := ⟨i - 1, by omega⟩
    rw [pow_succ', mul_smul, pow_smul_vert C.l_shift t (s - (t + 1) + 1) (by omega),
      show s - (t + 1) + 1 + t = s by omega]
  rw [tx_natCast, mul_smul, inv_smul_eq_iff, hr, hl] at h
  exact R.shift_last_ne C h

end RegData

end CFSG.Quasithin.Fan86.Tutte.Geo
