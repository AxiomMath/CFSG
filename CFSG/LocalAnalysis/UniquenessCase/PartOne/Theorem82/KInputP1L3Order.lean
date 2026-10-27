module

public import CFSG.Blueprint.Catalog
public import CFSG.Timmesfeld.Orders.ClassicalLinearThree
public import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

theorem card_of_lieModel_three {Y : Type} [Group Y] {ℓ f : ℕ}
    (h : (ℓ ^ f % 3 = 2 ∧ CFSG.Blueprint.LieModel Y .PSL 3 ℓ f) ∨
      (ℓ ^ f % 3 = 1 ∧ CFSG.Blueprint.LieModel Y .PSU 3 ℓ f)) :
    ℓ.Prime ∧ 1 ≤ f ∧ ∃ c : ℕ, (c = (ℓ ^ f) ^ 3 - 1 ∨ c = (ℓ ^ f) ^ 3 + 1) ∧
      Nat.card Y = (ℓ ^ f) ^ 3 * (((ℓ ^ f) ^ 2 - 1) * c) := by
  rcases h with ⟨h3, hY⟩ | ⟨h3, hY⟩
  · obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hY.statedClassicalModel_of_ne_zero (by norm_num)
    have hcard := CFSG.Timmesfeld.ClassicalOrders.card_psl_three_mul_gcd (K := K)
    have hg : Nat.gcd 3 (ℓ ^ f - 1) = 1 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
    rw [hK, hg, mul_one] at hcard
    exact ⟨hp, hf, _, Or.inl rfl, (Nat.card_congr e.toEquiv).trans hcard⟩
  · obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hY.statedClassicalModel_of_ne_zero (by norm_num)
    have hcard := CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd hp hf hK
    have hg : Nat.gcd 3 (ℓ ^ f + 1) = 1 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
    rw [hg, mul_one] at hcard
    exact ⟨hp, hf, _, Or.inr rfl, (Nat.card_congr e.toEquiv).trans hcard⟩

theorem odd_five_le_pow {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (h2 : ℓ ≠ 2)
    (h3 : ℓ ^ f % 3 = 1 ∨ ℓ ^ f % 3 = 2) : ℓ ^ f % 2 = 1 ∧ 5 ≤ ℓ ^ f := by
  have hodd : ℓ % 2 = 1 := (hℓ.eq_two_or_odd).resolve_left h2
  have hpow : ℓ ^ f % 2 = 1 := by rw [Nat.pow_mod, hodd]; simp
  have hge : ℓ ≤ ℓ ^ f := Nat.le_self_pow (by omega) ℓ
  have h3le : 3 ≤ ℓ := by have := hℓ.two_le; omega
  exact ⟨hpow, by omega⟩

theorem card_alt_fin_small {n : ℕ} (h : n = 5 ∨ n = 6 ∨ n = 8) :
    Nat.card (alternatingGroup (Fin n)) = 60 ∨ Nat.card (alternatingGroup (Fin n)) = 360 ∨
      Nat.card (alternatingGroup (Fin n)) = 20160 := by
  rcases h with rfl | rfl | rfl
  · left
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  · right; left
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  · right; right
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]

theorem center_alt_fin_small {n : ℕ} (h : n = 5 ∨ n = 6 ∨ n = 8) :
    Subgroup.center (alternatingGroup (Fin n)) = ⊥ := by
  apply alternatingGroup.center_eq_bot
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
