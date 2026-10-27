module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5ArithLab
public import CFSG.Quasithin.Recognition.Stroth.Str83G5ArithBasic

import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.Stroth.G5

variable {n : ℕ}

private def wt (n : ℕ) (δ : Bool) : ZMod (2 ^ n - 1) := if δ then cen n else 1

private theorem wt_true : wt n true = cen n := rfl

private theorem wt_false : wt n false = 1 := rfl

private theorem sgn_true : sgn (n := n) true = -1 := rfl

private theorem sgn_false : sgn (n := n) false = 1 := rfl

private theorem sgn_mul_sgn (a b : Bool) :
    sgn (n := n) a * sgn (n := n) b = sgn (n := n) (xor a b) := by
  cases a <;> cases b <;> simp [sgn_true, sgn_false]

private theorem sgn_mul_self (a : Bool) : sgn (n := n) a * sgn (n := n) a = 1 := by
  cases a <;> simp [sgn_true, sgn_false]

private theorem sgn_mul_xor (a b : Bool) :
    sgn (n := n) b * sgn (n := n) (xor a b) = sgn (n := n) a := by
  cases a <;> cases b <;> simp [sgn_true, sgn_false]

private theorem isUnit_sgn (a : Bool) : IsUnit (sgn (n := n) a) := by
  cases a
  · rw [sgn_false]; exact isUnit_one
  · rw [sgn_true]; exact isUnit_one.neg

private theorem isUnit_wt (hn : Odd n) (δ : Bool) : IsUnit (wt n δ) := by
  cases δ
  · rw [wt_false]; exact isUnit_one
  · rw [wt_true]; exact isUnit_cen hn

private theorem smul_neg_vec (a : ZMod (2 ^ n - 1)) (v : Coord n) : a • -v = -(a • v) := by
  ext <;> simp

private theorem neg_one_smul_vec (v : Coord n) : (-1 : ZMod (2 ^ n - 1)) • v = -v := by
  ext <;> simp

private theorem isUnit_link (hn : Odd n) (h5 : 5 ≤ n) (u : ℕ) (η δ : Bool) :
    IsUnit ((2 : ZMod (2 ^ n - 1)) ^ u * sgn (n := n) η * wt n δ) :=
  (((isUnit_two (by omega)).pow u).mul (isUnit_sgn η)).mul (isUnit_wt hn δ)

private theorem bool_xor_eq_false {a b : Bool} (h : xor a b = false) : a = b := by
  revert h; cases a <;> cases b <;> simp

private theorem cancel_sgn {g a₁ a₂ : ZMod (2 ^ n - 1)} (hg : IsUnit g) {ε₁ ε₂ : Bool}
    (h₁ : a₁ = g * sgn (n := n) ε₁) (h₂ : a₂ = g * sgn (n := n) ε₂) {x v : Coord n}
    (h : a₂ • x = a₁ • v) : x = sgn (n := n) (xor ε₁ ε₂) • v := by
  subst h₁ h₂
  have hu : IsUnit (g * sgn (n := n) ε₂) := hg.mul (isUnit_sgn ε₂)
  refine hu.smul_left_cancel.mp ?_
  rw [h, smul_smul]
  congr 1
  have := sgn_mul_xor (n := n) ε₁ ε₂
  linear_combination (-g) * this

private theorem two_pow_sq_inj (hn : Odd n) {u v : ℕ}
    (h : (2 : ZMod (2 ^ n - 1)) ^ (2 * u) = 2 ^ (2 * v)) :
    (2 : ZMod (2 ^ n - 1)) ^ u = 2 ^ v := by
  obtain ⟨a, ha⟩ := hn
  have key : ∀ w : ℕ, (2 : ZMod (2 ^ n - 1)) ^ w = (2 ^ (2 * w)) ^ (a + 1) := by
    intro w
    rw [← pow_mul, show 2 * w * (a + 1) = n * w + w by rw [ha]; ring, pow_add, pow_mul,
      two_pow_self, one_pow, one_mul]
  rw [key u, key v, h]

private theorem two_pow_mul_cen_sq_ne (hn : Odd n) (h5 : 5 ≤ n) (a b : ℕ) :
    (2 : ZMod (2 ^ n - 1)) ^ a * cen n ^ 2 ≠ 2 ^ b := by
  intro h
  refine cen_sq_ne_two_pow hn h5 (a * (n - 1) + b) ?_
  have hn1 : a * n = a * (n - 1) + a := by
    conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ n by omega)]
    rw [Nat.mul_add, mul_one]
  have h1 : (2 : ZMod (2 ^ n - 1)) ^ (a * n) = 1 := by
    rw [pow_mul', two_pow_self, one_pow]
  have h2 : (2 : ZMod (2 ^ n - 1)) ^ (a * n) = 2 ^ (a * (n - 1)) * 2 ^ a := by
    rw [← pow_add, hn1]
  calc cen n ^ 2 = 2 ^ (a * n) * cen n ^ 2 := by rw [h1, one_mul]
    _ = 2 ^ (a * (n - 1)) * (2 ^ a * cen n ^ 2) := by rw [h2]; ring
    _ = 2 ^ (a * (n - 1) + b) := by rw [h, ← pow_add]

private theorem weight_sq_eq (hn : Odd n) (h5 : 5 ≤ n) {u v : ℕ} {δ δ' : Bool}
    (h : ((2 : ZMod (2 ^ n - 1)) ^ u * wt n δ) ^ 2 = (2 ^ v * wt n δ') ^ 2) :
    δ = δ' ∧ (2 : ZMod (2 ^ n - 1)) ^ u = 2 ^ v := by
  have e2 : ∀ w : ℕ, ((2 : ZMod (2 ^ n - 1)) ^ w) ^ 2 = 2 ^ (2 * w) := fun w => by
    rw [← pow_mul, mul_comm]
  cases δ <;> cases δ' <;> simp only [wt_true, wt_false, mul_one, mul_pow, e2] at h
  · exact ⟨rfl, two_pow_sq_inj hn h⟩
  · exact absurd h.symm (two_pow_mul_cen_sq_ne hn h5 (2 * v) (2 * u))
  · exact absurd h (two_pow_mul_cen_sq_ne hn h5 (2 * u) (2 * v))
  · have hc : IsUnit (cen n ^ 2) := (isUnit_cen hn).pow 2
    exact ⟨rfl, two_pow_sq_inj hn (hc.mul_right_cancel h)⟩

section Aux

variable (k₀ m₀ : ZMod (2 ^ n - 1))

private def Apsi (s : ℤ) (η : Bool) : Prop :=
  mPow k₀ m₀ s (psi m₀) = sgn (n := n) η • psi m₀

private def Achi (s : ℤ) (η : Bool) : Prop :=
  mPow k₀ m₀ s (chi k₀) = sgn (n := n) η • chi k₀

private theorem eig_neg_psi (a b : ZMod (2 ^ n - 1)) (s : ℤ)
    (h : a • mPow k₀ m₀ s (psi m₀) = b • psi m₀) :
    a • mPow k₀ m₀ (-s) (psi m₀) = b • psi m₀ := by
  have h1 := congrArg (sigma1 m₀) h
  rw [sigma1_smul, sigma1_smul, sigma1_mPow_psi, sigma1_psi, smul_neg_vec, smul_neg_vec] at h1
  exact neg_injective h1

private theorem eig_sq_psi (a b : ZMod (2 ^ n - 1)) (s : ℤ)
    (h : a • mPow k₀ m₀ s (psi m₀) = b • psi m₀) : a ^ 2 = b ^ 2 := by
  have h1 := eig_neg_psi k₀ m₀ a b s h
  have h2 := congrArg (mPow k₀ m₀ (-s)) h
  rw [mPow_smul, mPow_smul, mPow_neg_mPow] at h2
  have h3 : (a * a) • psi m₀ = (b * b) • psi m₀ := by
    rw [mul_smul, h2, smul_comm a b, h1, mul_smul]
  have h4 := congrArg Prod.fst h3
  simpa [sq] using h4

private theorem eig_neg_chi (a b : ZMod (2 ^ n - 1)) (s : ℤ)
    (h : a • mPow k₀ m₀ s (chi k₀) = b • chi k₀) :
    a • mPow k₀ m₀ (-s) (chi k₀) = b • chi k₀ := by
  have h1 := congrArg (sigma2 k₀) h
  rw [sigma2_smul, sigma2_smul, sigma2_mPow_chi, sigma2_chi, smul_neg_vec, smul_neg_vec] at h1
  exact neg_injective h1

private theorem eig_sq_chi (a b : ZMod (2 ^ n - 1)) (s : ℤ)
    (h : a • mPow k₀ m₀ s (chi k₀) = b • chi k₀) : a ^ 2 = b ^ 2 := by
  have h1 := eig_neg_chi k₀ m₀ a b s h
  have h2 := congrArg (mPow k₀ m₀ (-s)) h
  rw [mPow_smul, mPow_smul, mPow_neg_mPow] at h2
  have h3 : (a * a) • chi k₀ = (b * b) • chi k₀ := by
    rw [mul_smul, h2, smul_comm a b, h1, mul_smul]
  have h4 := congrArg Prod.snd h3
  simpa [sq] using h4

private theorem apsi_zero (h3 : 3 ≤ n) (η : Bool) : Apsi k₀ m₀ 0 η ↔ η = false := by
  unfold Apsi
  cases η
  · simp [sgn_false]
  · rw [sgn_true, mPow_zero]
    simp only [Bool.true_eq_false, iff_false]
    intro h
    have h1 := congrArg Prod.fst h
    simp only [Prod.smul_fst, smul_eq_mul, psi_fst] at h1
    exact two_ne_zero' h3 (by linear_combination h1)

private theorem achi_zero (h3 : 3 ≤ n) (η : Bool) : Achi k₀ m₀ 0 η ↔ η = false := by
  unfold Achi
  cases η
  · simp [sgn_false]
  · rw [sgn_true, mPow_zero]
    simp only [Bool.true_eq_false, iff_false]
    intro h
    have h1 := congrArg Prod.snd h
    simp only [Prod.smul_snd, smul_eq_mul, chi_snd] at h1
    exact two_ne_zero' h3 (by linear_combination h1)

private theorem apsi_add {s s' : ℤ} {η η' : Bool} (h : Apsi k₀ m₀ s η) (h' : Apsi k₀ m₀ s' η') :
    Apsi k₀ m₀ (s + s') (xor η η') := by
  unfold Apsi at *
  rw [mPow_add, h', mPow_smul, h, smul_smul, mul_comm, sgn_mul_sgn]

private theorem achi_add {s s' : ℤ} {η η' : Bool} (h : Achi k₀ m₀ s η) (h' : Achi k₀ m₀ s' η') :
    Achi k₀ m₀ (s + s') (xor η η') := by
  unfold Achi at *
  rw [mPow_add, h', mPow_smul, h, smul_smul, mul_comm, sgn_mul_sgn]

private theorem apsi_neg {s : ℤ} {η : Bool} (h : Apsi k₀ m₀ s η) : Apsi k₀ m₀ (-s) η := by
  unfold Apsi at *
  have := eig_neg_psi k₀ m₀ 1 (sgn η) s (by rw [one_smul]; exact h)
  rwa [one_smul] at this

private theorem achi_neg {s : ℤ} {η : Bool} (h : Achi k₀ m₀ s η) : Achi k₀ m₀ (-s) η := by
  unfold Achi at *
  have := eig_neg_chi k₀ m₀ 1 (sgn η) s (by rw [one_smul]; exact h)
  rwa [one_smul] at this

end Aux

private theorem bool_aux : ∀ ε₁ ε₂ e a b : Bool, xor ε₁ ε₂ = (e && b) →
    xor ε₁ (e && a) = xor ε₂ (e && xor a b) := by decide

private theorem exists_gen (A : ℤ → Bool → Prop) (h0 : ∀ η, A 0 η ↔ η = false)
    (hadd : ∀ s s' η η', A s η → A s' η' → A (s + s') (xor η η'))
    (hneg : ∀ s η, A s η → A (-s) η) (Δ : ℕ) :
    ∃ (r : ℕ) (e : Bool), (r = 0 → e = false) ∧ r ≤ Δ ∧ (0 < r → A r e) ∧
      (0 < r → ∀ s η, A s η → (r : ℤ) ∣ s ∧ η = (e && decide (Odd (s / r)))) ∧
      (r = 0 → ∀ s η, A s η → |s| ≤ (Δ : ℤ) → s = 0 ∧ η = false) := by
  classical
  by_cases hex : ∃ r : ℕ, 0 < r ∧ r ≤ Δ ∧ ∃ η, A r η
  · obtain ⟨r, ⟨hr0, hrΔ, e, he⟩, hmin⟩ : ∃ r : ℕ, (0 < r ∧ r ≤ Δ ∧ ∃ η, A r η) ∧
        ∀ r' : ℕ, r' < r → ¬ (0 < r' ∧ r' ≤ Δ ∧ ∃ η, A r' η) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun r' h => Nat.find_min hex h⟩
    have hrz : (0 : ℤ) < r := by exact_mod_cast hr0
    have hq : ∀ q : ℕ, A ((q : ℤ) * r) (e && decide (Odd q)) := by
      intro q
      induction q with
      | zero =>
        have h00 : decide (Odd 0) = false := by decide
        simp only [Nat.cast_zero, zero_mul, h00, Bool.and_false]
        exact (h0 false).mpr rfl
      | succ q ih =>
        have h1 := hadd _ _ _ _ ih he
        have e1 : ((q + 1 : ℕ) : ℤ) * r = (q : ℤ) * r + r := by push_cast; ring
        have e2 : xor (e && decide (Odd q)) e = (e && decide (Odd (q + 1))) := by
          by_cases hq : Odd q <;> cases e <;> simp [hq, Nat.odd_add_one]
        rw [e1, ← e2]
        exact h1
    have hqz : ∀ q : ℤ, A (q * r) (e && decide (Odd q)) := by
      intro q
      obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg q
      · simpa using hq k
      · have := hneg _ _ (hq k)
        rw [neg_mul]
        simpa using this
    refine ⟨r, e, fun h => absurd h hr0.ne', hrΔ, fun _ => he, ?_,
      fun h => absurd h hr0.ne'⟩
    intro _ s η hA
    have hmod : A (s % r) (xor η (e && decide (Odd (s / r)))) := by
      have h1 := hadd s (-((s / r) * r)) η _ hA (hneg _ _ (hqz (s / r)))
      have e1 : s + -((s / r) * r) = s % r := by
        have := Int.mul_ediv_add_emod s r
        linarith
      rw [e1] at h1
      exact h1
    have hmod0 : s % r = 0 := by
      by_contra hne
      have hnn : 0 ≤ s % r := Int.emod_nonneg _ hrz.ne'
      have hlt : s % r < r := Int.emod_lt_of_pos _ hrz
      have hpos : 0 < s % r := lt_of_le_of_ne hnn (Ne.symm hne)
      refine hmin (s % r).toNat (by omega)
        ⟨by omega, by omega, xor η (e && decide (Odd (s / r))), ?_⟩
      rw [Int.toNat_of_nonneg hnn]
      exact hmod
    refine ⟨Int.dvd_of_emod_eq_zero hmod0, ?_⟩
    rw [hmod0] at hmod
    have h1 := (h0 _).mp hmod
    revert h1
    cases η <;> cases e <;> cases decide (Odd (s / r)) <;> simp
  · push Not at hex
    refine ⟨0, false, fun _ => rfl, Nat.zero_le _, fun h => absurd h (lt_irrefl 0),
      fun h => absurd h (lt_irrefl 0), ?_⟩
    intro _ s η hA hs
    have hs0 : s = 0 := by
      by_contra hne
      obtain ⟨hs1, hs2⟩ := abs_le.mp hs
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h1 := hneg _ _ hA
        refine hex (-s).toNat (by omega) (by omega) η ?_
        rw [Int.toNat_of_nonneg (by omega)]
        exact h1
      · refine hex s.toNat (by omega) (by omega) η ?_
        rw [Int.toNat_of_nonneg (by omega)]
        exact hA
    subst hs0
    exact ⟨rfl, (h0 η).mp hA⟩

private theorem redA_eq {A : ℤ → Bool → Prop} {Δ r : ℕ} {e : Bool}
    (h0 : r = 0 → ∀ s η, A s η → |s| ≤ (Δ : ℤ) → s = 0 ∧ η = false)
    (h1 : 0 < r → ∀ s η, A s η → (r : ℤ) ∣ s ∧ η = (e && decide (Odd (s / r))))
    {t₁ t₂ : ℤ} {ε₁ ε₂ : Bool} (hA : A (t₂ - t₁) (xor ε₁ ε₂))
    (hb : r = 0 → |t₂ - t₁| ≤ (Δ : ℤ)) : redA r e t₁ ε₁ = redA r e t₂ ε₂ := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · obtain ⟨hs, hη⟩ := h0 hr _ _ hA (hb hr)
    have ht : t₁ = t₂ := by omega
    have hε : ε₁ = ε₂ := bool_xor_eq_false hη
    rw [ht, hε]
  · obtain ⟨⟨q, hq⟩, hη⟩ := h1 hr _ _ hA
    have hrne : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
    have ht : t₂ = t₁ + r * q := by linarith
    have hqq : (t₂ - t₁) / r = q := by rw [hq]; exact Int.mul_ediv_cancel_left q hrne
    rw [hqq] at hη
    have hdiv : t₂ / r = t₁ / r + q := by rw [ht, Int.add_mul_ediv_left _ _ hrne]
    have hmod : t₂ % r = t₁ % r := by rw [ht, Int.add_mul_emod_self_left]
    have hodd : decide (Odd (t₁ / r + q)) = xor (decide (Odd (t₁ / r))) (decide (Odd q)) := by
      by_cases h1 : Odd (t₁ / r) <;> by_cases h2 : Odd q <;>
        simp [h1, h2, Int.odd_add, ← Int.not_odd_iff_even]
    unfold redA
    rw [if_neg hr.ne', if_neg hr.ne', hmod, hdiv, hodd]
    rw [bool_aux ε₁ ε₂ e (decide (Odd (t₁ / r))) (decide (Odd q)) hη]

section Aux

variable (k₀ m₀ : ZMod (2 ^ n - 1))

private theorem val_psi (t : ℤ) (ε δ : Bool) :
    Lab.val k₀ m₀ ⟨true, t, ε, δ⟩ = (sgn ε * wt n δ) • mPow k₀ m₀ t (psi m₀) := by
  simp [Lab.val, wt, smul_smul]

private theorem val_chi (t : ℤ) (ε c : Bool) :
    Lab.val k₀ m₀ ⟨false, t, ε, c⟩ = (sgn ε * wt n false) • mPow k₀ m₀ t (chi k₀) := by
  simp [Lab.val, wt]

private theorem class_core (hn : Odd n) (h5 : 5 ≤ n) {v : Coord n}
    (hv : ∀ (a b : ZMod (2 ^ n - 1)) (s : ℤ), a • mPow k₀ m₀ s v = b • v → a ^ 2 = b ^ 2)
    {s : ℤ} {ε₁ ε₂ δ₁ δ₂ : Bool} {u : ℕ}
    (h : (sgn ε₂ * wt n δ₂) • mPow k₀ m₀ s v =
      ((2 : ZMod (2 ^ n - 1)) ^ u * (sgn ε₁ * wt n δ₁)) • v) :
    δ₁ = δ₂ ∧ mPow k₀ m₀ s v = sgn (n := n) (xor ε₁ ε₂) • v := by
  have hsq := hv _ _ _ h
  have hsq' : ((2 : ZMod (2 ^ n - 1)) ^ 0 * wt n δ₂) ^ 2 = (2 ^ u * wt n δ₁) ^ 2 := by
    have e1 := sgn_mul_self (n := n) ε₁
    have e2 := sgn_mul_self (n := n) ε₂
    linear_combination hsq + (2 ^ u * wt n δ₁) ^ 2 * e1 - (wt n δ₂) ^ 2 * e2
  obtain ⟨hδ, h2u⟩ := weight_sq_eq hn h5 hsq'
  refine ⟨hδ.symm, ?_⟩
  subst hδ
  rw [← h2u] at h
  exact cancel_sgn (isUnit_wt hn δ₂) (by rw [pow_zero]; ring) (by ring) h

private theorem psi_psi_class (hn : Odd n) (h5 : 5 ≤ n) {t₁ t₂ : ℤ} {ε₁ ε₂ δ₁ δ₂ : Bool}
    (h : cls (Lab.val k₀ m₀ ⟨true, t₁, ε₁, δ₁⟩) = cls (Lab.val k₀ m₀ ⟨true, t₂, ε₂, δ₂⟩)) :
    δ₁ = δ₂ ∧ Apsi k₀ m₀ (t₂ - t₁) (xor ε₁ ε₂) := by
  obtain ⟨u, hu⟩ := (cls_eq_cls_iff (by omega)).mp h
  rw [val_psi, val_psi] at hu
  have h2 := congrArg (mPow k₀ m₀ (-t₁)) hu
  rw [mPow_smul, mPow_smul, mPow_smul, mPow_neg_mPow, ← mPow_add, neg_add_eq_sub,
    ← mul_smul] at h2
  exact class_core k₀ m₀ hn h5 (eig_sq_psi k₀ m₀) h2

private theorem chi_chi_class (hn : Odd n) (h5 : 5 ≤ n) {t₁ t₂ : ℤ} {ε₁ ε₂ c₁ c₂ : Bool}
    (h : cls (Lab.val k₀ m₀ ⟨false, t₁, ε₁, c₁⟩) = cls (Lab.val k₀ m₀ ⟨false, t₂, ε₂, c₂⟩)) :
    Achi k₀ m₀ (t₂ - t₁) (xor ε₁ ε₂) := by
  obtain ⟨u, hu⟩ := (cls_eq_cls_iff (by omega)).mp h
  rw [val_chi, val_chi] at hu
  have h2 := congrArg (mPow k₀ m₀ (-t₁)) hu
  rw [mPow_smul, mPow_smul, mPow_smul, mPow_neg_mPow, ← mPow_add, neg_add_eq_sub,
    ← mul_smul] at h2
  exact (class_core k₀ m₀ hn h5 (eig_sq_chi k₀ m₀) (δ₁ := false) (δ₂ := false) h2).2

private theorem psi_chi_class (hn : Odd n) (h5 : 5 ≤ n) {t t' : ℤ} {ε ε' δ c : Bool}
    (h : cls (Lab.val k₀ m₀ ⟨true, t, ε, δ⟩) = cls (Lab.val k₀ m₀ ⟨false, t', ε', c⟩)) :
    ∃ u : ℕ, mPow k₀ m₀ (t' - t) (chi k₀) =
      ((2 : ZMod (2 ^ n - 1)) ^ u * sgn (n := n) (xor ε ε') * wt n δ) • psi m₀ := by
  obtain ⟨u, hu⟩ := (cls_eq_cls_iff (by omega)).mp h
  rw [val_psi, val_chi] at hu
  refine ⟨u, ?_⟩
  have h2 := congrArg (mPow k₀ m₀ (-t)) hu
  rw [mPow_smul, mPow_smul, mPow_smul, mPow_neg_mPow, ← mPow_add, neg_add_eq_sub,
    ← mul_smul] at h2
  have hu' : IsUnit (sgn (n := n) ε' * wt n false) := (isUnit_sgn ε').mul (isUnit_wt hn false)
  refine hu'.smul_left_cancel.mp ?_
  rw [h2, smul_smul]
  congr 1
  have := sgn_mul_xor (n := n) ε ε'
  rw [wt_false]
  linear_combination (-(2 ^ u * wt n δ)) * this

private theorem chi_of_link {L : ZMod (2 ^ n - 1)} {s : ℤ}
    (hl : mPow k₀ m₀ s (chi k₀) = L • psi m₀) :
    chi k₀ = L • mPow k₀ m₀ (-s) (psi m₀) := by
  have := congrArg (mPow k₀ m₀ (-s)) hl
  rwa [mPow_neg_mPow, mPow_smul] at this

private theorem link_apsi {L : ZMod (2 ^ n - 1)} (hL : IsUnit L) {s : ℤ}
    (hl : mPow k₀ m₀ s (chi k₀) = L • psi m₀) :
    mPow k₀ m₀ (2 * s + 1) (psi m₀) = psi m₀ := by
  have h1 := chi_of_link k₀ m₀ hl
  have h2 : mPow k₀ m₀ (-s) (chi k₀) = L • mPow k₀ m₀ 1 (psi m₀) := by
    have := congrArg (sigma2 k₀) hl
    rwa [sigma2_mPow_chi, sigma2_smul, sigma2_psi, smul_neg_vec, neg_inj] at this
  have h3 : mPow k₀ m₀ (-s) (chi k₀) = L • mPow k₀ m₀ (-s + -s) (psi m₀) := by
    rw [h1, mPow_smul, ← mPow_add]
  have h4 := hL.smul_left_cancel.mp (h3.symm.trans h2)
  have h5 := congrArg (mPow k₀ m₀ (2 * s)) h4
  rw [← mPow_add, ← mPow_add, show 2 * s + (-s + -s) = 0 by ring, mPow_zero] at h5
  exact h5.symm

private theorem link_iff {L : ZMod (2 ^ n - 1)} (hL : IsUnit L) {s : ℤ}
    (hl : mPow k₀ m₀ s (chi k₀) = L • psi m₀) (a : ℤ) (b : ZMod (2 ^ n - 1)) :
    mPow k₀ m₀ a (psi m₀) = b • psi m₀ ↔ mPow k₀ m₀ a (chi k₀) = b • chi k₀ := by
  have h1 := chi_of_link k₀ m₀ hl
  have comm : ∀ (x y : ℤ) (v : Coord n),
      mPow k₀ m₀ x (mPow k₀ m₀ y v) = mPow k₀ m₀ y (mPow k₀ m₀ x v) := by
    intro x y v
    rw [← mPow_add, ← mPow_add, add_comm]
  constructor
  · intro h
    rw [h1, mPow_smul, comm a (-s), h, mPow_smul, smul_comm]
  · intro h
    refine hL.smul_left_cancel.mp ?_
    rw [← mPow_smul, ← hl, comm, h, mPow_smul, hl, smul_comm]

private theorem link_unique (hn : Odd n) (h5 : 5 ≤ n) {s s' : ℤ} {u u' : ℕ} {η η' δ δ' : Bool}
    (hl : mPow k₀ m₀ s (chi k₀) =
      ((2 : ZMod (2 ^ n - 1)) ^ u * sgn (n := n) η * wt n δ) • psi m₀)
    (hl' : mPow k₀ m₀ s' (chi k₀) =
      ((2 : ZMod (2 ^ n - 1)) ^ u' * sgn (n := n) η' * wt n δ') • psi m₀) :
    δ = δ' ∧ Apsi k₀ m₀ (s' + -s) (xor η' η) := by
  have h1 := chi_of_link k₀ m₀ hl
  have h : ((2 : ZMod (2 ^ n - 1)) ^ u * sgn (n := n) η * wt n δ) • mPow k₀ m₀ (s' + -s) (psi m₀) =
      ((2 : ZMod (2 ^ n - 1)) ^ u' * sgn (n := n) η' * wt n δ') • psi m₀ := by
    rw [← hl', h1, mPow_smul, ← mPow_add]
  have hsq := eig_sq_psi k₀ m₀ _ _ _ h
  have hsq' : ((2 : ZMod (2 ^ n - 1)) ^ u * wt n δ) ^ 2 = (2 ^ u' * wt n δ') ^ 2 := by
    have e1 := sgn_mul_self (n := n) η
    have e2 := sgn_mul_self (n := n) η'
    linear_combination hsq + (2 ^ u' * wt n δ') ^ 2 * e2 - (2 ^ u * wt n δ) ^ 2 * e1
  obtain ⟨hδ, hu⟩ := weight_sq_eq hn h5 hsq'
  subst hδ
  refine ⟨rfl, ?_⟩
  unfold Apsi
  have hg : IsUnit ((2 : ZMod (2 ^ n - 1)) ^ u * wt n δ) :=
    ((isUnit_two (by omega)).pow u).mul (isUnit_wt hn δ)
  exact cancel_sgn hg (by rw [← hu]; ring) (by ring) h

end Aux

private theorem mem_bits {r : ℕ} {e : Bool} (he : r = 0 → e = false) :
    e ∈ (if r = 0 then [false] else [false, true]) := by
  by_cases h : r = 0
  · simp [h, he h]
  · cases e <;> simp [h]

private theorem mem_typeList_unlinked {Δ r r' : ℕ} {e e' : Bool} (hr : r ≤ Δ) (hr' : r' ≤ Δ)
    (he : r = 0 → e = false) (he' : r' = 0 → e' = false) :
    AType.unlinked r e r' e' ∈ typeList Δ := by
  unfold typeList
  rw [List.mem_append]
  left
  rw [List.mem_flatMap]
  refine ⟨r, List.mem_range.mpr (by omega), ?_⟩
  rw [List.mem_flatMap]
  refine ⟨e, mem_bits he, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨r', List.mem_range.mpr (by omega), ?_⟩
  rw [List.mem_map]
  exact ⟨e', mem_bits he', rfl⟩

private theorem mem_typeList_linked {Δ r : ℕ} {ε₀ δ₀ : Bool} (hr : Odd r) (hrΔ : r ≤ 2 * Δ + 1) :
    AType.linked r ε₀ δ₀ ∈ typeList Δ := by
  unfold typeList
  rw [List.mem_append]
  right
  rw [List.mem_flatMap]
  refine ⟨r, ?_, ?_⟩
  · rw [List.mem_map]
    obtain ⟨k, hk⟩ := hr
    exact ⟨k, List.mem_range.mpr (by omega), by omega⟩
  · rw [List.mem_flatMap]
    refine ⟨ε₀, by cases ε₀ <;> simp, ?_⟩
    rw [List.mem_map]
    exact ⟨δ₀, by cases δ₀ <;> simp, rfl⟩

section Aux

variable (k₀ m₀ : ZMod (2 ^ n - 1))

private def HasLink : Prop :=
  ∃ (s : ℤ) (u : ℕ) (η δ : Bool), mPow k₀ m₀ s (chi k₀) =
    ((2 : ZMod (2 ^ n - 1)) ^ u * sgn (n := n) η * wt n δ) • psi m₀

private theorem linked_gen (hn : Odd n) (h5 : 5 ≤ n) {r : ℕ} (hr : 0 < r) {e : Bool}
    (hgen : ∀ s η, Apsi k₀ m₀ s η → (r : ℤ) ∣ s ∧ η = (e && decide (Odd (s / r))))
    {s₀ : ℤ} {L : ZMod (2 ^ n - 1)} (hL : IsUnit L)
    (hl : mPow k₀ m₀ s₀ (chi k₀) = L • psi m₀) :
    Odd r ∧ (∃ j : ℤ, 2 * s₀ + 1 = r * (2 * j + 1)) ∧
      ∀ s η, Apsi k₀ m₀ s η → (r : ℤ) ∣ s ∧ η = false := by
  have hA0 : Apsi k₀ m₀ (2 * s₀ + 1) false := by
    unfold Apsi
    rw [sgn_false, one_smul]
    exact link_apsi k₀ m₀ hL hl
  obtain ⟨⟨q, hq⟩, he⟩ := hgen _ _ hA0
  have hrne : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
  have hodd : Odd ((r : ℤ) * q) := by rw [← hq]; exact ⟨s₀, rfl⟩
  obtain ⟨hr1, hq1⟩ := Int.odd_mul.mp hodd
  have hdiv : (2 * s₀ + 1) / r = q := by rw [hq]; exact Int.mul_ediv_cancel_left q hrne
  rw [hdiv, decide_eq_true hq1, Bool.and_true] at he
  obtain ⟨j, hj⟩ := hq1
  refine ⟨(Int.odd_coe_nat r).mp hr1, ⟨j, by rw [hq, hj]⟩, fun s η hs => ?_⟩
  obtain ⟨hd, hη⟩ := hgen s η hs
  refine ⟨hd, ?_⟩
  rw [hη, ← he]
  simp

private theorem no_mixed (hn : Odd n) (h5 : 5 ≤ n) {Δ r : ℕ}
    (hlk : ¬ (HasLink k₀ m₀ ∧ 0 < r))
    (hr0 : r = 0 → ∀ s η, Apsi k₀ m₀ s η → |s| ≤ ((2 * Δ + 1 : ℕ) : ℤ) → s = 0 ∧ η = false)
    {t t' : ℤ} {ε ε' δ c : Bool} (hb : |t - t'| ≤ (Δ : ℤ))
    (h : cls (Lab.val k₀ m₀ ⟨true, t, ε, δ⟩) = cls (Lab.val k₀ m₀ ⟨false, t', ε', c⟩)) :
    False := by
  obtain ⟨u, hu⟩ := psi_chi_class k₀ m₀ hn h5 h
  have hr : r = 0 := by
    by_contra hne
    exact hlk ⟨⟨_, u, _, _, hu⟩, Nat.pos_of_ne_zero hne⟩
  have hA : Apsi k₀ m₀ (2 * (t' - t) + 1) false := by
    unfold Apsi
    rw [sgn_false, one_smul]
    exact link_apsi k₀ m₀ (isUnit_link hn h5 u _ _) hu
  have hbb : |2 * (t' - t) + 1| ≤ ((2 * Δ + 1 : ℕ) : ℤ) := by
    rw [abs_le] at hb ⊢
    omega
  have := (hr0 hr _ _ hA hbb).1
  omega

private theorem linked_canon (hn : Odd n) (h5 : 5 ≤ n) {r : ℕ} (hr : 0 < r) {e : Bool}
    (hgen : ∀ s η, Apsi k₀ m₀ s η → (r : ℤ) ∣ s ∧ η = (e && decide (Odd (s / r))))
    {s₀ : ℤ} {u₀ : ℕ} {η₀ δ₀ : Bool}
    (hl : mPow k₀ m₀ s₀ (chi k₀) =
      ((2 : ZMod (2 ^ n - 1)) ^ u₀ * sgn (n := n) η₀ * wt n δ₀) • psi m₀)
    (l₁ l₂ : Lab) (h : cls (l₁.val k₀ m₀) = cls (l₂.val k₀ m₀)) :
    (AType.linked r η₀ δ₀).canon l₁ = (AType.linked r η₀ δ₀).canon l₂ := by
  obtain ⟨hodd, ⟨j, hj⟩, hg⟩ := linked_gen k₀ m₀ hn h5 hr hgen (isUnit_link hn h5 u₀ η₀ δ₀) hl
  have hmod : ∀ x y : ℤ, (r : ℤ) ∣ x - y → x % r = y % r := fun x y hxy =>
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hxy)
  have key_pp : ∀ {t₁ t₂ : ℤ} {ε₁ ε₂ c₁ c₂ : Bool},
      cls (Lab.val k₀ m₀ ⟨true, t₁, ε₁, c₁⟩) = cls (Lab.val k₀ m₀ ⟨true, t₂, ε₂, c₂⟩) →
      c₁ = c₂ ∧ ε₁ = ε₂ ∧ t₁ % r = t₂ % r := by
    intro t₁ t₂ ε₁ ε₂ c₁ c₂ h
    obtain ⟨hc, hA⟩ := psi_psi_class k₀ m₀ hn h5 h
    obtain ⟨hd, hη⟩ := hg _ _ hA
    exact ⟨hc, bool_xor_eq_false hη, hmod _ _ (dvd_sub_comm.mp hd)⟩
  have key_cc : ∀ {t₁ t₂ : ℤ} {ε₁ ε₂ c₁ c₂ : Bool},
      cls (Lab.val k₀ m₀ ⟨false, t₁, ε₁, c₁⟩) = cls (Lab.val k₀ m₀ ⟨false, t₂, ε₂, c₂⟩) →
      ε₁ = ε₂ ∧ (r : ℤ) ∣ t₁ - t₂ := by
    intro t₁ t₂ ε₁ ε₂ c₁ c₂ h
    have hA := chi_chi_class k₀ m₀ hn h5 h
    have hA' : Apsi k₀ m₀ (t₂ - t₁) (xor ε₁ ε₂) := by
      unfold Achi at hA
      unfold Apsi
      exact (link_iff k₀ m₀ (isUnit_link hn h5 u₀ η₀ δ₀) hl _ _).mpr hA
    obtain ⟨hd, hη⟩ := hg _ _ hA'
    exact ⟨bool_xor_eq_false hη, dvd_sub_comm.mp hd⟩
  have key_pc : ∀ {t t' : ℤ} {ε ε' δ c : Bool},
      cls (Lab.val k₀ m₀ ⟨true, t, ε, δ⟩) = cls (Lab.val k₀ m₀ ⟨false, t', ε', c⟩) →
      (AType.linked r η₀ δ₀).canon ⟨true, t, ε, δ⟩ =
        (AType.linked r η₀ δ₀).canon ⟨false, t', ε', c⟩ := by
    intro t t' ε ε' δ c h
    obtain ⟨u, hu⟩ := psi_chi_class k₀ m₀ hn h5 h
    obtain ⟨hδ, hA⟩ := link_unique k₀ m₀ hn h5 hl hu
    obtain ⟨⟨a, ha⟩, hη⟩ := hg _ _ hA
    obtain ⟨k, hk⟩ := hodd
    have hkz : (r : ℤ) = 2 * k + 1 := by exact_mod_cast hk
    have hh : (((r + 1) / 2 : ℕ) : ℤ) = k + 1 := by omega
    have hε : ε = xor ε' η₀ := by
      revert hη; cases ε <;> cases ε' <;> cases η₀ <;> simp
    simp only [AType.canon, Lab.mk.injEq, true_and]
    refine ⟨hmod _ _ ⟨-(a + j + 1), ?_⟩, hε, hδ.symm⟩
    rw [hh]
    linarith
  rcases l₁ with ⟨_ | _, t₁, ε₁, c₁⟩ <;> rcases l₂ with ⟨_ | _, t₂, ε₂, c₂⟩
  · obtain ⟨hε, hd⟩ := key_cc h
    simp only [AType.canon, Lab.mk.injEq, true_and]
    refine ⟨hmod _ _ ?_, by rw [hε], trivial⟩
    rwa [add_sub_add_right_eq_sub]
  · exact (key_pc h.symm).symm
  · exact key_pc h
  · obtain ⟨hc, hε, hm⟩ := key_pp h
    simp only [AType.canon, Lab.mk.injEq, true_and]
    exact ⟨hm, hε, hc⟩

end Aux

theorem exists_type (hn : Odd n) (h5 : 5 ≤ n) (k₀ m₀ : ZMod (2 ^ n - 1)) (Δ : ℕ) :
    ∃ τ ∈ typeList Δ,
      (∀ l₁ l₂ : Lab, |l₁.t - l₂.t| ≤ (Δ : ℤ) → cls (l₁.val k₀ m₀) = cls (l₂.val k₀ m₀) →
        τ.canon l₁ = τ.canon l₂) ∧
      ∀ r r' : ℕ, τ = .unlinked r true r' true → 0 < r → 0 < r' →
        mPow k₀ m₀ r (psi m₀) = -psi m₀ ∧ mPow k₀ m₀ r' (chi k₀) = -chi k₀ := by
  have h3 : 3 ≤ n := by omega
  obtain ⟨r, e, hr0, hrΔ, hrA, hrgen, hr0gen⟩ :=
    exists_gen (Apsi k₀ m₀) (apsi_zero k₀ m₀ h3) (fun _ _ _ _ => apsi_add k₀ m₀)
      (fun _ _ => apsi_neg k₀ m₀) (2 * Δ + 1)
  by_cases hlk : HasLink k₀ m₀ ∧ 0 < r
  · obtain ⟨⟨s₀, u₀, η₀, δ₀, hl⟩, hr⟩ := hlk
    obtain ⟨hodd, -, -⟩ := linked_gen k₀ m₀ hn h5 hr (hrgen hr) (isUnit_link hn h5 u₀ η₀ δ₀) hl
    refine ⟨.linked r η₀ δ₀, mem_typeList_linked hodd hrΔ, ?_, ?_⟩
    · intro l₁ l₂ _ h
      exact linked_canon k₀ m₀ hn h5 hr (hrgen hr) hl l₁ l₂ h
    · intro a b h
      cases h
  · obtain ⟨r₁, e₁, hr₁0, hr₁Δ, hr₁A, hr₁gen, hr₁0gen⟩ :=
      exists_gen (Apsi k₀ m₀) (apsi_zero k₀ m₀ h3) (fun _ _ _ _ => apsi_add k₀ m₀)
        (fun _ _ => apsi_neg k₀ m₀) Δ
    obtain ⟨r₂, e₂, hr₂0, hr₂Δ, hr₂A, hr₂gen, hr₂0gen⟩ :=
      exists_gen (Achi k₀ m₀) (achi_zero k₀ m₀ h3) (fun _ _ _ _ => achi_add k₀ m₀)
        (fun _ _ => achi_neg k₀ m₀) Δ
    refine ⟨.unlinked r₁ e₁ r₂ e₂, mem_typeList_unlinked hr₁Δ hr₂Δ hr₁0 hr₂0, ?_, ?_⟩
    · rintro ⟨_ | _, t₁, ε₁, c₁⟩ ⟨_ | _, t₂, ε₂, c₂⟩ hb h
      · have hb' : |t₂ - t₁| ≤ (Δ : ℤ) := by rw [abs_sub_comm]; exact hb
        have hA := chi_chi_class k₀ m₀ hn h5 h
        have hred := redA_eq hr₂0gen hr₂gen hA (fun _ => hb')
        simp only [AType.canon, hred]
      · have hb' : |t₂ - t₁| ≤ (Δ : ℤ) := by rw [abs_sub_comm]; exact hb
        exact (no_mixed k₀ m₀ hn h5 hlk hr0gen hb' h.symm).elim
      · exact (no_mixed k₀ m₀ hn h5 hlk hr0gen hb h).elim
      · have hb' : |t₂ - t₁| ≤ (Δ : ℤ) := by rw [abs_sub_comm]; exact hb
        obtain ⟨hc, hA⟩ := psi_psi_class k₀ m₀ hn h5 h
        have hred := redA_eq hr₁0gen hr₁gen hA (fun _ => hb')
        simp only [AType.canon, hred, hc]
    · intro a b hτ ha hb
      obtain ⟨rfl, rfl, rfl, rfl⟩ : r₁ = a ∧ e₁ = true ∧ r₂ = b ∧ e₂ = true := by
        simpa [eq_comm] using hτ
      refine ⟨?_, ?_⟩
      · have := hr₁A ha
        unfold Apsi at this
        rw [this, sgn_true, neg_one_smul_vec]
      · have := hr₂A hb
        unfold Achi at this
        rw [this, sgn_true, neg_one_smul_vec]

end CFSG.Quasithin.Stroth.G5

end
