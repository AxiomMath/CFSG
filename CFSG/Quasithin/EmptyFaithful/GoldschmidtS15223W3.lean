module

public import CFSG.Quasithin.EmptyFaithful.S152NWreath

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace S15223

open S152N S152N.W3

noncomputable local instance instFintypeW3 : Fintype W3 :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).symm

local instance instDecEqW3 : DecidableEq W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

local instance instDecMemN0 : DecidablePred (· ∈ N0) := fun a =>
  inferInstanceAs (Decidable (a.right = 1 ∧ ∀ q, a.left q * a.left q * a.left q = 1))

instance instFiniteW3 : Finite W3 := Finite.of_fintype W3

theorem mem_N0_of_pow_nine : ∀ w : W3, w ^ 9 = 1 → w ∈ N0 := by
  decide +kernel

theorem pow_three_of_mem_N0 : ∀ w : W3, w ∈ N0 → w ^ 3 = 1 := by
  decide +kernel

theorem N0_comm : ∀ a b : W3, a ∈ N0 → b ∈ N0 → a * b = b * a := by
  decide +kernel

theorem oTwoUpper_top_eq_N0 : oTwoUpper (⊤ : Subgroup W3) = N0 := by
  apply le_antisymm
  · refine (Subgroup.closure_le N0).mpr fun x hx => ?_
    have hdvd : orderOf x ∣ 9 * 8 := by
      have := orderOf_dvd_natCard x
      rwa [W3.card_eq] at this
    have hcop : Nat.Coprime (orderOf x) 8 := by
      have h2 : Nat.Coprime (orderOf x) 2 := Nat.coprime_two_right.mpr hx.2
      exact Nat.Coprime.pow_right 3 h2
    exact mem_N0_of_pow_nine x (orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hdvd))
  · intro n hn
    refine mem_oTwoUpper_of_odd (Subgroup.mem_top n) ?_
    exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one (pow_three_of_mem_N0 n hn))

theorem eq_bot_or_eq_N0_of_sylow {P C : Subgroup W3} (hP : IsSylowTwoOf P ⊤) (hC : C ≤ N0)
    (hinv : ∀ p ∈ P, ∀ c ∈ C, p * c * p⁻¹ ∈ C) : C = ⊥ ∨ C = N0 := by
  have hconj : ∀ n ∈ N0, ∀ c ∈ N0, n * c * n⁻¹ = c := fun n hn c hc => by
    rw [N0_comm n c hn hc, mul_assoc, mul_inv_cancel, mul_one]
  have hPS : P ≤ Subgroup.normalizer (C : Set W3) := fun p hp =>
    Subgroup.mem_normalizer_iff.mpr fun c =>
      ⟨hinv p hp c, fun h => by
        have e : p⁻¹ * (p * c * p⁻¹) * p⁻¹⁻¹ = c := by group
        exact e ▸ hinv p⁻¹ (P.inv_mem hp) _ h⟩
  have hN0S : N0 ≤ Subgroup.normalizer (C : Set W3) := fun n hn =>
    Subgroup.mem_normalizer_iff.mpr fun c => by
      constructor
      · intro hc
        rw [hconj n hn c (hC hc)]
        exact hc
      · intro h
        have h1 := hconj n⁻¹ (N0.inv_mem hn) _ (hC h)
        have e : n⁻¹ * (n * c * n⁻¹) * n⁻¹⁻¹ = c := by group
        rw [e] at h1
        rw [h1]
        exact h
  rcases sylow_maximal hP hPS with h | h
  · exfalso
    have hle : N0 ≤ P := h ▸ hN0S
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP.2.1
    have h9 : 9 ∣ Nat.card P := card_N0 ▸ Subgroup.card_dvd_of_le hle
    rw [hk] at h9
    have h3 : 3 ∣ 2 ^ k := Nat.dvd_trans (by norm_num) h9
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  · refine N0_irred hC fun p _ c hc => ?_
    have hp : p ∈ Subgroup.normalizer (C : Set W3) := h ▸ Subgroup.mem_top p
    exact (Subgroup.mem_normalizer_iff.mp hp c).mp hc

end S15223

end CFSG.Quasithin
