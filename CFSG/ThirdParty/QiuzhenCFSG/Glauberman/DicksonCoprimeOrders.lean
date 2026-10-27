module

public import Mathlib.GroupTheory.OrderOfElement

namespace CFSG
end CFSG
open CFSG

/-!
# Coprime order lemmas for Dickson families
-/

namespace CFSG.Glauberman
namespace Dickson

universe u

public theorem hmem_eq_one_of_coprime_card
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card B))
    {x : G} (hxA : x ∈ A) (hxB : x ∈ B) :
    x = 1 := by
  have horder_A : orderOf x ∣ Nat.card A := by
    simpa [Subgroup.orderOf_coe] using
      (orderOf_dvd_natCard (⟨x, hxA⟩ : A))
  have horder_B : orderOf x ∣ Nat.card B := by
    simpa [Subgroup.orderOf_coe] using
      (orderOf_dvd_natCard (⟨x, hxB⟩ : B))
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcoprime horder_A horder_B)

public theorem hq_coprime_split_order (q : ℕ) (hq : 1 ≤ q) :
    Nat.Coprime q ((q - 1) / Nat.gcd (q - 1) 2) := by
  apply ((Nat.coprime_self_sub_right hq).mpr (Nat.coprime_one_right q)).coprime_dvd_right
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (q - 1) 2)

public theorem hq_coprime_nonsplit_order (q : ℕ) (hq : 1 ≤ q) :
    Nat.Coprime q ((q + 1) / Nat.gcd (q - 1) 2) := by
  apply ((Nat.coprime_self_add_right).mpr (Nat.coprime_one_right q)).coprime_dvd_right
  apply Nat.div_dvd_of_dvd
  convert Nat.dvd_add (Nat.gcd_dvd_left (q - 1) 2)
    (Nat.gcd_dvd_right (q - 1) 2) using 1
  all_goals omega

public theorem hsplit_nonsplit_order_coprime (q : ℕ) (hq : 2 ≤ q) :
    Nat.Coprime
      ((q - 1) / Nat.gcd (q - 1) 2)
      ((q + 1) / Nat.gcd (q - 1) 2) := by
  by_cases hq_even : Even q
  · have hq_sub_one_odd : Odd (q - 1) := by
      rw [← Nat.not_even_iff_odd]
      intro heven
      have hparity := (Nat.even_sub (by omega : 1 ≤ q)).mp heven
      exact Nat.not_even_one (hparity.mp hq_even)
    have hgcd : Nat.gcd (q - 1) 2 = 1 :=
      Nat.coprime_iff_gcd_eq_one.mp hq_sub_one_odd.coprime_two_right
    rw [hgcd]
    simp only [Nat.div_one]
    have hcop : Nat.Coprime (q - 1) ((q - 1) + 2) :=
      (Nat.coprime_self_add_right).mpr hq_sub_one_odd.coprime_two_right
    convert hcop using 1
    all_goals omega
  · have hq_odd : Odd q := Nat.not_even_iff_odd.mp hq_even
    have htwo_dvd : 2 ∣ q - 1 := by
      rcases hq_odd with ⟨k, hk⟩
      use k
      omega
    have hgcd : Nat.gcd (q - 1) 2 = 2 :=
      Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
        (Nat.dvd_gcd htwo_dvd (dvd_refl 2))
    rcases hq_odd with ⟨k, hk⟩
    rw [hgcd]
    have hsub : q - 1 = 2 * k := by omega
    have hadd : q + 1 = 2 * (k + 1) := by omega
    rw [hsub, hadd]
    rw [Nat.mul_div_cancel_left k (by omega),
      Nat.mul_div_cancel_left (k + 1) (by omega)]
    exact (Nat.coprime_self_add_right).mpr (Nat.coprime_one_right k)

end Dickson
end CFSG.Glauberman

