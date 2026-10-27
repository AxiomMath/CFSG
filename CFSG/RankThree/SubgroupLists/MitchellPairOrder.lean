module

public import CFSG.RankThree.SubgroupLists.SymplecticPartThreeBase
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

public section

namespace CFSG.RankThree.SubgroupLists

open CFSG.Assembly.LowTwoRank

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

section PowerTable

variable {A : Type*} [Ring A] [Algebra K A] {x : A} {β : K}

theorem pow_three_of_mul_self_eq (hx : x * x = (2 * β) • x - 1) :
    x ^ 3 = (4 * β ^ 2 - 1) • x - (2 * β) • 1 := by
  rw [pow_succ, pow_two, hx, sub_mul, smul_mul_assoc, hx, one_mul]
  module

theorem pow_four_of_mul_self_eq (hx : x * x = (2 * β) • x - 1) :
    x ^ 4 = (4 * β * (2 * β ^ 2 - 1)) • x + (1 - 4 * β ^ 2) • 1 := by
  rw [pow_succ, pow_three_of_mul_self_eq hx, sub_mul, smul_mul_assoc, smul_mul_assoc, hx, one_mul]
  module

theorem pow_five_of_mul_self_eq (hx : x * x = (2 * β) • x - 1) :
    x ^ 5 = (16 * β ^ 4 - 12 * β ^ 2 + 1) • x + (4 * β - 8 * β ^ 3) • 1 := by
  rw [pow_succ, pow_four_of_mul_self_eq hx, add_mul, smul_mul_assoc, smul_mul_assoc, hx, one_mul]
  module

end PowerTable

theorem mul_sq_of_isNCInv (h2 : (2 : K) ≠ 0) {d e : GL V₄ K} (hd : IsNCInv d) (he : IsNCInv e) :
    (d : Matrix V₄ V₄ K) * e * ((d : Matrix V₄ V₄ K) * e) =
      (2 * cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K)) • ((d : Matrix V₄ V₄ K) * e) - 1 :=
  mul_sq_of_involutions h2 (mem_cliffSpace_of_involution h2 hd.1 hd.2.1 hd.2.2.1 hd.2.2.2).1
    (mem_cliffSpace_of_involution h2 he.1 he.2.1 he.2.2.1 he.2.2.2).1
    (by rw [← Units.val_mul, hd.2.1, Units.val_one])
    (by rw [← Units.val_mul, he.2.1, Units.val_one])

theorem eq_or_eq_neg_of_mul_eq_smul_one {d e : GL V₄ K} (hd2 : d * d = 1) (he2 : e * e = 1)
    {c : K} (h : (d : Matrix V₄ V₄ K) * e = c • 1) : e = d ∨ e = -d := by
  have hdd : (d : Matrix V₄ V₄ K) * d = 1 := by rw [← Units.val_mul, hd2, Units.val_one]
  have hee : (e : Matrix V₄ V₄ K) * e = 1 := by rw [← Units.val_mul, he2, Units.val_one]
  have he : (e : Matrix V₄ V₄ K) = c • (d : Matrix V₄ V₄ K) := by
    calc (e : Matrix V₄ V₄ K) = (d : Matrix V₄ V₄ K) * ((d : Matrix V₄ V₄ K) * e) := by
          rw [← Matrix.mul_assoc, hdd, Matrix.one_mul]
      _ = c • (d : Matrix V₄ V₄ K) := by rw [h, Matrix.mul_smul, Matrix.mul_one]
  have hc : c * c = 1 := by
    have h1 : (c * c) • (1 : Matrix V₄ V₄ K) = 1 := by
      calc (c * c) • (1 : Matrix V₄ V₄ K) = (e : Matrix V₄ V₄ K) * e := by
            rw [he, Matrix.smul_mul, Matrix.mul_smul, hdd, smul_smul]
        _ = 1 := hee
    simpa using congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 0)
  rcases mul_self_eq_one_iff.mp hc with rfl | rfl
  · exact Or.inl (Units.ext (by rw [he, one_smul]))
  · exact Or.inr (Units.ext (by rw [he, Units.val_neg, neg_one_smul]))

theorem isThreePair_or_of_pow_eq_one_or_neg (h2 : (2 : K) ≠ 0) {d e : GL V₄ K} (hd : IsNCInv d)
    (he : IsNCInv e) {k : ℕ} (hk1 : 1 ≤ k) (hk6 : k < 6)
    (hk : (d * e) ^ k = 1 ∨ (d * e) ^ k = -1) :
    IsThreePair d e ∨ cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K) ^ 2 = 2⁻¹ ∨
      16 * cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K) ^ 4 -
        12 * cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K) ^ 2 + 1 = 0 := by
  have hsq := mul_sq_of_isNCInv h2 hd he
  set β := cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K)
  set X : Matrix V₄ V₄ K := (d : Matrix V₄ V₄ K) * e with hX
  have hval : (((d * e) ^ k : GL V₄ K) : Matrix V₄ V₄ K) = X ^ k := by
    rw [hX, Units.val_pow_eq_pow_val, Units.val_mul]
  obtain ⟨ε, hε⟩ : ∃ ε : K, X ^ k = ε • (1 : Matrix V₄ V₄ K) := by
    rcases hk with h | h
    · exact ⟨1, by rw [← hval, h, Units.val_one, one_smul]⟩
    · exact ⟨-1, by rw [← hval, h, Units.val_neg, Units.val_one, neg_one_smul]⟩
  have hscal : ∀ a b : K, X ^ k = a • X + b • 1 → a ≠ 0 → IsThreePair d e := by
    intro a b hab ha
    have haX : a • X = (ε - b) • (1 : Matrix V₄ V₄ K) := by
      rw [sub_smul, ← hε, hab, add_sub_cancel_right]
    have hX1 : X = (a⁻¹ * (ε - b)) • (1 : Matrix V₄ V₄ K) := by
      rw [mul_smul, ← haX, smul_smul, inv_mul_cancel₀ ha, one_smul]
    rcases eq_or_eq_neg_of_mul_eq_smul_one hd.2.1 he.2.1 hX1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  interval_cases k
  · exact Or.inl (hscal 1 0 (by rw [pow_one]; module) one_ne_zero)
  · by_cases ha : 2 * β = 0
    · exact Or.inl (Or.inr (Or.inr (Or.inl ((mul_eq_zero.mp ha).resolve_left h2))))
    · exact Or.inl (hscal _ (-1) (by rw [pow_two, hsq]; module) ha)
  · by_cases ha : 4 * β ^ 2 - 1 = 0
    · have hf : (2 * β - 1) * (2 * β + 1) = 0 := by linear_combination ha
      rcases mul_eq_zero.mp hf with h | h
      · have h' : (2 : K) * β = 1 := by linear_combination h
        exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right h').symm))))
      · have h' : (2 : K) * -β = 1 := by linear_combination -h
        have h'' : β = -2⁻¹ := by rw [inv_eq_of_mul_eq_one_right h', neg_neg]
        exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h''))))
    · exact Or.inl (hscal _ (-(2 * β)) (by rw [pow_three_of_mul_self_eq hsq]; module) ha)
  · by_cases ha : 4 * β * (2 * β ^ 2 - 1) = 0
    · rcases mul_eq_zero.mp ha with h | h
      · exact Or.inl (Or.inr (Or.inr (Or.inl ((mul_eq_zero.mp h).resolve_left h4))))
      · have h' : (2 : K) * β ^ 2 = 1 := by linear_combination h
        exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right h').symm)
    · exact Or.inl (hscal _ _ (pow_four_of_mul_self_eq hsq) ha)
  · by_cases ha : 16 * β ^ 4 - 12 * β ^ 2 + 1 = 0
    · exact Or.inr (Or.inr ha)
    · exact Or.inl (hscal _ _ (pow_five_of_mul_self_eq hsq) ha)

theorem pow_four_eq_neg_one_of_sq_eq_half (h2 : (2 : K) ≠ 0) {d e : GL V₄ K} (hd : IsNCInv d)
    (he : IsNCInv e) (hβ : cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K) ^ 2 = 2⁻¹) :
    (d * e) ^ 4 = -1 := by
  have h4 := pow_four_of_mul_self_eq (mul_sq_of_isNCInv h2 hd he)
  set β := cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K)
  have hinv : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have ha : 4 * β * (2 * β ^ 2 - 1) = 0 := by linear_combination 8 * β * hβ + 4 * β * hinv
  have hb : 1 - 4 * β ^ 2 = -1 := by linear_combination (-4) * hβ - 2 * hinv
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_mul, h4, ha, hb, zero_smul, zero_add, neg_one_smul,
    Units.val_neg, Units.val_one]

theorem pow_five_eq_one_or_neg_of_quartic (h2 : (2 : K) ≠ 0) {d e : GL V₄ K} (hd : IsNCInv d)
    (he : IsNCInv e)
    (hβ : 16 * cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K) ^ 4 -
      12 * cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K) ^ 2 + 1 = 0) :
    (d * e) ^ 5 = 1 ∨ (d * e) ^ 5 = -1 := by
  have h5 := pow_five_of_mul_self_eq (mul_sq_of_isNCInv h2 hd he)
  set β := cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K)
  rw [hβ, zero_smul, zero_add] at h5
  have hb : (4 * β - 8 * β ^ 3) * (4 * β - 8 * β ^ 3) = 1 := by
    linear_combination (4 * β ^ 2 - 1) * hβ
  rcases mul_self_eq_one_iff.mp hb with hb | hb
  · left
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mul, h5, hb, one_smul, Units.val_one]
  · right
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mul, h5, hb, neg_one_smul, Units.val_neg,
      Units.val_one]

theorem mod_eight_of_sq_eq_half {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {β : ZMod p}
    (hβ : β ^ 2 = 2⁻¹) : p % 8 = 1 ∨ p % 8 = 7 := by
  refine (ZMod.exists_sq_eq_two_iff hp2).mp ⟨2 * β, ?_⟩
  rw [mul_mul_mul_comm, ← sq β, hβ, mul_inv_cancel_right₀ (two_ne_zero_of_charP hp2)]

theorem sq_eq_one_of_quartic_of_eq_five {p : ℕ} [Fact p.Prime] (hp : p = 5) {β : ZMod p}
    (hβ : 16 * β ^ 4 - 12 * β ^ 2 + 1 = 0) : β ^ 2 = 1 := by
  have h5 : (5 : ZMod p) = 0 := by
    subst hp
    exact_mod_cast ZMod.natCast_self 5
  have h : (β ^ 2 - 1) ^ 2 = 0 := by linear_combination hβ - (3 * β ^ 4 - 2 * β ^ 2) * h5
  linear_combination (pow_eq_zero_iff two_ne_zero).mp h

end CFSG.RankThree.SubgroupLists
