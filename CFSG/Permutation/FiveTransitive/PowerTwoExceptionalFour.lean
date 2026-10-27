module

public import CFSG.Permutation.FiveTransitive.FreeComplementOrbitCount
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG

namespace FiveTransitive.PowerTwoExceptionalFour

open MulAction

private theorem power_eq_four (k : ℕ) (hlo : 4 ≤ 2 ^ k) (hdiv : 8 ∣ 2 ^ k - 4) :
    2 ^ k = 4 := by
  by_cases hk : k ≤ 2
  · interval_cases k <;> norm_num at *
  · have h8 : 8 ∣ 2 ^ k := by
      change 2 ^ 3 ∣ 2 ^ k
      exact Nat.pow_dvd_pow 2 (by omega)
    omega

theorem card_eq_four
    {H Y : Type*} [Group H] [Finite H] [Finite Y] [MulAction H Y]
    (hH : 8 ∣ Nat.card H) (k : ℕ) (hk : Nat.card Y = 2 ^ k)
    (E : Set Y) (hE : E.ncard = 4)
    (hstable : ∀ (h : H) (y : Y), y ∈ E → h • y ∈ E)
    (hfree : ∀ (h : H) (y : Y), y ∉ E → h • y = y → h = 1) :
    Nat.card Y = 4 := by
  let D : SubMulAction H Y :=
    { carrier := Eᶜ
      smul_mem' h y hy := by
        intro hh
        have ht := hstable h⁻¹ (h • y) hh
        exact hy (by simpa only [inv_smul_smul] using ht) }
  have hfreeD : ∀ (h : H) (y : D), h • y = y → h = 1 := by
    intro h y hh
    exact hfree h y.val y.property (congrArg Subtype.val hh)
  have hdiv : Nat.card H ∣ Nat.card D := by
    rw [FreeComplementOrbitCount.card_eq_mul_orbits hfreeD]
    exact dvd_mul_right _ _
  have hD : Nat.card D = Nat.card Y - 4 := by
    change Nat.card ↥Eᶜ = _
    rw [Nat.card_coe_set_eq, Set.ncard_compl, hE]
  have hlo : 4 ≤ Nat.card Y := by
    rw [← hE]
    exact Set.ncard_le_card E
  rw [hk] at hlo
  rw [hD, hk] at hdiv
  exact hk.trans (power_eq_four k hlo (hH.trans hdiv))

end FiveTransitive.PowerTwoExceptionalFour

end CFSG
