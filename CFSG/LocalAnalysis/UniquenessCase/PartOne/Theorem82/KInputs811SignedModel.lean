module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedModel

open CFSG.Open CFSG.GroupTheory Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
  (IsSignedCoords LieFam811 qMinusPi qPlusPi)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.ModelTransport (ModelK6rRank ModelK7Dvd)

theorem qMinusPi_eq_minusPi (r f : ℕ) : qMinusPi r f = SignedFacts.minusPi (r ^ f) := rfl

theorem qPlusPi_eq_plusPi (r f : ℕ) : qPlusPi r f = SignedFacts.plusPi (r ^ f) := rfl

theorem qMinusPi_of_mod_two {r f : ℕ} (h : r ^ f % 3 = 2) : qMinusPi r f = r ^ f + 1 := by
  unfold qMinusPi
  rw [if_neg (by omega)]

theorem qPlusPi_of_mod_two {r f : ℕ} (h : r ^ f % 3 = 2) : qPlusPi r f = r ^ f - 1 := by
  unfold qPlusPi
  rw [if_neg (by omega)]

theorem qMinusPi_of_mod_one {r f : ℕ} (h : r ^ f % 3 = 1) : qMinusPi r f = r ^ f - 1 := by
  unfold qMinusPi
  rw [if_pos h]

theorem qPlusPi_of_mod_one {r f : ℕ} (h : r ^ f % 3 = 1) : qPlusPi r f = r ^ f + 1 := by
  unfold qPlusPi
  rw [if_pos h]

theorem not_dvd_sub_one_of_dvd_add_one {p q : ℕ} (hp5 : 5 ≤ p) (hq : 1 ≤ q) (h : p ∣ q + 1) :
    ¬ p ∣ q - 1 := fun h' => by
  have h2 : p ∣ 2 := by
    have := Nat.dvd_sub h h'
    rwa [show q + 1 - (q - 1) = 2 by omega] at this
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem not_dvd_add_one_of_dvd_sub_one {p q : ℕ} (hp5 : 5 ≤ p) (hq : 1 ≤ q) (h : p ∣ q - 1) :
    ¬ p ∣ q + 1 := fun h' => not_dvd_sub_one_of_dvd_add_one hp5 hq h' h

theorem not_dvd_six {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ 6 := fun h => by
  have := Nat.le_of_dvd (by norm_num) h
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

@[expose] def SignedModelK6c (Y : Type) [Group Y] : Prop :=
  ∃ (H : Type) (_ : Group H) (_ : Finite H) (N : Subgroup H) (_ : N.Normal)
    (c₀ : Multiplicative (Fin 3 → ZMod 3) →* H) (_ : Y ⧸ center Y ≃* H ⧸ N),
    IsSignedCoords c₀.range c₀ ∧ ¬ 3 ∣ Nat.card N ∧ UniqueElemSylow 3 3 (H ⧸ N)

@[expose] def SignedModelK6r (Y : Type) [Group Y] (r : ℕ) : Prop :=
  ∃ (H : Type) (_ : Group H) (_ : Finite H) (N : Subgroup H) (_ : N.Normal)
    (c₀ : Multiplicative (Fin 3 → ZMod 3) →* H) (_ : Y ⧸ center Y ≃* H ⧸ N),
    IsSignedCoords c₀.range c₀ ∧ ¬ 3 ∣ Nat.card N ∧ UniqueElemSylow 3 3 (H ⧸ N) ∧
    (5 ≤ r → ¬ r ∣ Nat.card N ∧ ModelK6rRank c₀ r)

@[expose] def SignedModelK7 (Y : Type) [Group Y] (fam : LieFam811) (r f : ℕ) : Prop :=
  ∃ (H : Type) (_ : Group H) (_ : Finite H) (N : Subgroup H) (_ : N.Normal)
    (c₀ : Multiplicative (Fin 3 → ZMod 3) →* H) (_ : Y ⧸ center Y ≃* H ⧸ N),
    IsSignedCoords c₀.range c₀ ∧ ¬ 3 ∣ Nat.card N ∧ UniqueElemSylow 3 3 (H ⧸ N) ∧
    (∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ qMinusPi r f →
      ¬ p ∣ Nat.card N ∧ 2 ≤ CFSG.Open.pRank p (centralizer (c₀.range : Set H))) ∧
    ((fam = .l6 ∨ fam = .l7) → ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ qPlusPi r f →
      2 ≤ CFSG.Open.pRank p
        (centralizer ((c₀.range.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)))) ∧
    ((fam = .psp6 ∨ fam = .omega7) → ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ qPlusPi r f →
      ¬ p ∣ Nat.card N ∧ ModelK7Dvd c₀ p)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedModel
