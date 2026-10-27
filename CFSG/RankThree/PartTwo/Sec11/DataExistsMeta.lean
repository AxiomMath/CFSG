module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace Metacyclic

theorem geom_sum_three_mul (l : ℤ) (n : ℕ) :
    ∑ i ∈ Finset.range (3 * n), l ^ i =
      (∑ i ∈ Finset.range n, l ^ i) * (1 + l ^ n + l ^ (2 * n)) := by
  have h3 : 3 * n = n + n + n := by ring
  rw [h3, Finset.sum_range_add, Finset.sum_range_add]
  have e1 : ∑ i ∈ Finset.range n, l ^ (n + i) = l ^ n * ∑ i ∈ Finset.range n, l ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => pow_add l n i
  have e2 : ∑ i ∈ Finset.range n, l ^ (n + n + i) =
      l ^ (2 * n) * ∑ i ∈ Finset.range n, l ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_add, two_mul]
  rw [e1, e2]
  ring

theorem exists_geom_sum_eq_three_pow_mul {l : ℤ} (hl : (3 : ℤ) ∣ l - 1) (j : ℕ) :
    ∃ u : ℤ, ∑ i ∈ Finset.range (3 ^ j), l ^ i = 3 ^ j * u ∧ ¬ (3 : ℤ) ∣ u := by
  induction j with
  | zero => exact ⟨1, by simp, by norm_num⟩
  | succ j ih =>
    obtain ⟨u, hu, hu3⟩ := ih
    have hμ : (3 : ℤ) ∣ l ^ 3 ^ j - 1 := by
      have := sub_dvd_pow_sub_pow l 1 (3 ^ j)
      rw [one_pow] at this
      exact hl.trans this
    obtain ⟨w, hw⟩ := hμ
    have hl' : l ^ 3 ^ j = 1 + 3 * w := by linarith
    have e : 3 ^ (j + 1) = 3 * 3 ^ j := by rw [pow_succ, mul_comm]
    refine ⟨u * (1 + 3 * (w + w ^ 2)), ?_, ?_⟩
    · rw [e, geom_sum_three_mul, hu, pow_mul', hl']
      ring
    · intro h
      rcases Int.prime_three.dvd_or_dvd h with h1 | h1
      · exact hu3 h1
      · have h2 : (3 : ℤ) ∣ 3 * (w + w ^ 2) := dvd_mul_right 3 _
        have h3 : (3 : ℤ) ∣ 1 := (Int.dvd_add_left h2).mp h1
        norm_num at h3

theorem three_dvd_sub_one_of_dvd_pow {l : ℤ} {N : ℕ} (h : (3 : ℤ) ∣ l ^ 3 ^ N - 1) :
    (3 : ℤ) ∣ l - 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h' : ((l ^ 3 ^ N - 1 : ℤ) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast h)
  have e : ((l - 1 : ℤ) : ZMod 3) = 0 := by
    push_cast at h' ⊢
    rwa [ZMod.pow_card_pow] at h'
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp e

theorem three_pow_dvd_of_dvd {m j : ℕ} {l t₀ u' : ℤ} (hP : ¬ (3 : ℤ) ^ m ∣ (l - 1) * 3 ^ j)
    (hQ : (3 : ℤ) ^ m ∣ t₀ * (3 * u') * (l - 1)) (hu' : ¬ (3 : ℤ) ∣ u') :
    (3 : ℤ) ^ j ∣ t₀ := by
  by_cases ht : t₀ = 0
  · rw [ht]
    exact dvd_zero _
  have hP' : ¬ 3 ^ m ∣ (l - 1).natAbs * 3 ^ j := by
    intro h
    apply hP
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow]
    exact h
  have hQ' : 3 ^ m ∣ t₀.natAbs * (3 * u'.natAbs) * (l - 1).natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hQ
    rwa [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow] at this
  have hu'' : ¬ 3 ∣ u'.natAbs := by
    intro h
    apply hu'
    exact Int.natCast_dvd.mpr h
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_pow]
  change 3 ^ j ∣ t₀.natAbs
  obtain ⟨k, n', hn', hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr ht) 3
    (by norm_num)
  have hcop3 : Nat.Coprime 3 (n' * u'.natAbs) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h =>
      ((Nat.Prime.dvd_mul Nat.prime_three).mp h).elim hn' hu''
  have hcop : Nat.Coprime (3 ^ m) (n' * u'.natAbs) := Nat.Coprime.pow_left m hcop3
  have h1 : 3 ^ m ∣ 3 ^ (k + 1) * (l - 1).natAbs := by
    have e : t₀.natAbs * (3 * u'.natAbs) * (l - 1).natAbs =
        (n' * u'.natAbs) * (3 ^ (k + 1) * (l - 1).natAbs) := by
      rw [hk]
      ring
    rw [e] at hQ'
    exact hcop.dvd_of_dvd_mul_left hQ'
  by_contra hkj
  have hkj' : k + 1 ≤ j := by
    by_contra h
    apply hkj
    rw [hk]
    exact Dvd.dvd.mul_right (Nat.pow_dvd_pow 3 (by omega)) _
  apply hP'
  refine h1.trans ?_
  rw [mul_comm]
  exact Nat.mul_dvd_mul_left _ (Nat.pow_dvd_pow 3 hkj')

theorem exists_dvd_mul_add {m j N : ℕ} {l μ t₀ : ℤ} (h1 : (3 : ℤ) ^ m ∣ l ^ 3 ^ N - 1)
    (h3 : ¬ (3 : ℤ) ^ m ∣ μ - 1) (h4 : (3 : ℤ) ^ m ∣ l ^ 3 ^ j - μ)
    (h5 : (3 : ℤ) ^ m ∣ t₀ * (1 + μ + μ ^ 2) * (l - 1)) :
    ∃ t : ℤ, (3 : ℤ) ^ m ∣ t * l * ∑ i ∈ Finset.range (3 ^ j), l ^ i + t₀ := by
  have hm : m ≠ 0 := by
    rintro rfl
    exact h3 (by simp)
  have h3m : (3 : ℤ) ∣ (3 : ℤ) ^ m := dvd_pow_self 3 hm
  have hl : (3 : ℤ) ∣ l - 1 := three_dvd_sub_one_of_dvd_pow (h3m.trans h1)
  obtain ⟨u, hu, hu3⟩ := exists_geom_sum_eq_three_pow_mul hl j
  have hlj : (3 : ℤ) ∣ l ^ 3 ^ j - 1 := by
    have := sub_dvd_pow_sub_pow l 1 (3 ^ j)
    rw [one_pow] at this
    exact hl.trans this
  have hμ : (3 : ℤ) ∣ μ - 1 := by
    have e : μ - 1 = (l ^ 3 ^ j - 1) - (l ^ 3 ^ j - μ) := by ring
    rw [e]
    exact dvd_sub hlj (h3m.trans h4)
  obtain ⟨w, hw⟩ := hμ
  have hμ' : 1 + μ + μ ^ 2 = 3 * (1 + 3 * (w + w ^ 2)) := by
    rw [show μ = 1 + 3 * w by linarith]
    ring
  have hu'3 : ¬ (3 : ℤ) ∣ 1 + 3 * (w + w ^ 2) := by
    intro h
    have h2 : (3 : ℤ) ∣ 3 * (w + w ^ 2) := dvd_mul_right 3 _
    have : (3 : ℤ) ∣ 1 := (Int.dvd_add_left h2).mp h
    norm_num at this
  have hP : ¬ (3 : ℤ) ^ m ∣ (l - 1) * 3 ^ j := by
    intro h
    apply h3
    have e1 : l ^ 3 ^ j - 1 = (l - 1) * 3 ^ j * u := by
      rw [← mul_geom_sum, hu]
      ring
    have e2 : μ - 1 = (l ^ 3 ^ j - 1) - (l ^ 3 ^ j - μ) := by ring
    rw [e2, e1]
    exact dvd_sub (h.mul_right u) h4
  rw [hμ'] at h5
  obtain ⟨t₁, ht₁⟩ := three_pow_dvd_of_dvd hP h5 hu'3
  have hlu : IsCoprime (l * u) ((3 : ℤ) ^ m) := by
    refine IsCoprime.pow_right ?_
    rw [Int.isCoprime_iff_gcd_eq_one]
    have hl3 : ¬ (3 : ℤ) ∣ l := by
      intro h
      have : (3 : ℤ) ∣ 1 := by
        have e : (1 : ℤ) = l - (l - 1) := by ring
        rw [e]
        exact dvd_sub h hl
      norm_num at this
    have hn : ¬ (3 : ℤ) ∣ l * u := fun h => (Int.prime_three.dvd_or_dvd h).elim hl3 hu3
    have := Int.gcd_dvd_right (l * u) 3
    have h3' : Int.gcd (l * u) 3 ∣ 3 := by exact_mod_cast this
    rcases (Nat.dvd_prime Nat.prime_three).mp h3' with h | h
    · exact h
    · exfalso
      apply hn
      have := Int.gcd_dvd_left (l * u) 3
      rw [h] at this
      exact_mod_cast this
  obtain ⟨α, β, hαβ⟩ := hlu
  refine ⟨-t₁ * α, ⟨t₁ * β * 3 ^ j, ?_⟩⟩
  rw [hu, ht₁]
  linear_combination (-(3 : ℤ) ^ j * t₁) * hαβ

variable {G : Type*} [Group G]

theorem pow_mul_zpow_mul_inv_pow {x r : G} {l : ℤ} (hrx : r * x * r⁻¹ = x ^ l) (k : ℕ)
    (t : ℤ) : r ^ k * x ^ t * (r ^ k)⁻¹ = x ^ (t * l ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : r ^ (k + 1) * x ^ t * (r ^ (k + 1))⁻¹ =
        r * (r ^ k * x ^ t * (r ^ k)⁻¹) * r⁻¹ := by
      rw [pow_succ', mul_inv_rev]
      group
    rw [e, ih, ← conj_zpow, hrx, ← zpow_mul, pow_succ]
    congr 1
    ring

theorem mul_zpow_pow_eq {x r : G} {l : ℤ} (hrx : r * x * r⁻¹ = x ^ l) (t : ℤ) (n : ℕ) :
    (r * x ^ t) ^ n = x ^ (t * l * ∑ i ∈ Finset.range n, l ^ i) * r ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := pow_mul_zpow_mul_inv_pow hrx (n + 1) t
    have e : x ^ (t * l * ∑ i ∈ Finset.range n, l ^ i) * r ^ n * (r * x ^ t) =
        x ^ (t * l * ∑ i ∈ Finset.range n, l ^ i) *
          (r ^ (n + 1) * x ^ t * (r ^ (n + 1))⁻¹) * r ^ (n + 1) := by
      rw [pow_succ r n]
      group
    rw [pow_succ (r * x ^ t) n, ih, e, h, ← zpow_add, Finset.sum_range_succ]
    congr 2
    rw [pow_succ]
    ring

theorem mul_pow_three_eq (v a : G) :
    (v * a) ^ 3 = v * (a * v * a⁻¹) * (a ^ 2 * v * (a ^ 2)⁻¹) * a ^ 3 := by
  simp only [pow_succ, pow_zero, one_mul]
  group

end Metacyclic

open Metacyclic

variable {G : Type*} [Group G]

theorem exists_mul_zpow_pow_eq_zpow_mul {x s r a : G} {m j N : ℕ} {l κ μ ν t₀ w₀ : ℤ}
    (hx : orderOf x = 3 ^ m) (hsx : s * x = x * s)
    (hxs : ∀ i k : ℤ, x ^ i = s ^ k → x ^ i = 1)
    (hrx : r * x * r⁻¹ = x ^ l) (hrs : r * s * r⁻¹ = s ^ κ)
    (hax : a * x * a⁻¹ = x ^ μ) (has : a * s * a⁻¹ = s ^ ν)
    (hr3 : r ^ 3 ^ N = 1) (ha3 : a ^ 3 = 1) (hax' : a * x ≠ x * a)
    (hra : r ^ 3 ^ j = x ^ t₀ * s ^ w₀ * a) :
    ∃ t : ℤ, (r * x ^ t) ^ 3 ^ j = s ^ w₀ * a := by
  have hdvd : ∀ e : ℤ, x ^ e = 1 ↔ (3 : ℤ) ^ m ∣ e := by
    intro e
    rw [← orderOf_dvd_iff_zpow_eq_one, hx]
    push_cast
    rfl
  have hcs : ∀ i k : ℤ, s ^ k * x ^ i = x ^ i * s ^ k := fun i k =>
    ((Commute.zpow_zpow (show Commute s x from hsx) k i)).eq
  have hmul : ∀ i k i' k' : ℤ, x ^ i * s ^ k * (x ^ i' * s ^ k') = x ^ (i + i') * s ^ (k + k') := by
    intro i k i' k'
    calc x ^ i * s ^ k * (x ^ i' * s ^ k') = x ^ i * (s ^ k * x ^ i') * s ^ k' := by group
      _ = x ^ i * (x ^ i' * s ^ k) * s ^ k' := by rw [hcs]
      _ = x ^ (i + i') * s ^ (k + k') := by rw [zpow_add, zpow_add]; group
  have h1 : (3 : ℤ) ^ m ∣ l ^ 3 ^ N - 1 := by
    rw [← hdvd]
    have h := pow_mul_zpow_mul_inv_pow hrx (3 ^ N) 1
    rw [hr3, one_mul, inv_one, mul_one, zpow_one, one_mul] at h
    rw [zpow_sub, zpow_one, ← h, mul_inv_cancel]
  have h3 : ¬ (3 : ℤ) ^ m ∣ μ - 1 := by
    intro h
    apply hax'
    have hμ : x ^ μ = x := by
      rw [← sub_add_cancel μ 1, zpow_add, (hdvd _).mpr h, one_mul, zpow_one]
    calc a * x = (a * x * a⁻¹) * a := by group
      _ = x * a := by rw [hax, hμ]
  have h4 : (3 : ℤ) ^ m ∣ l ^ 3 ^ j - μ := by
    rw [← hdvd]
    have h := pow_mul_zpow_mul_inv_pow hrx (3 ^ j) 1
    have e : x ^ t₀ * s ^ w₀ * a * x ^ (1 : ℤ) * (x ^ t₀ * s ^ w₀ * a)⁻¹ = x ^ μ := by
      calc x ^ t₀ * s ^ w₀ * a * x ^ (1 : ℤ) * (x ^ t₀ * s ^ w₀ * a)⁻¹
          = x ^ t₀ * s ^ w₀ * (a * x * a⁻¹) * (s ^ w₀)⁻¹ * (x ^ t₀)⁻¹ := by group
        _ = x ^ t₀ * (s ^ w₀ * x ^ μ) * (s ^ w₀)⁻¹ * (x ^ t₀)⁻¹ := by rw [hax]; group
        _ = x ^ μ := by rw [hcs]; group
    rw [hra, e, one_mul] at h
    rw [zpow_sub, ← h, mul_inv_cancel]
  have hconj : ∀ k : ℕ, a ^ k * (x ^ t₀ * s ^ w₀) * (a ^ k)⁻¹ =
      x ^ (t₀ * μ ^ k) * s ^ (w₀ * ν ^ k) := by
    intro k
    rw [← pow_mul_zpow_mul_inv_pow hax k t₀, ← pow_mul_zpow_mul_inv_pow has k w₀]
    group
  have hcube : r ^ (3 ^ j * 3) =
      x ^ (t₀ * (1 + μ + μ ^ 2)) * s ^ (w₀ * (1 + ν + ν ^ 2)) := by
    have h1' := hconj 1
    rw [pow_one] at h1'
    rw [pow_mul, hra, mul_pow_three_eq (x ^ t₀ * s ^ w₀) a, h1', hconj 2, ha3, mul_one,
      hmul, hmul]
    congr 2 <;> ring
  have h5 : (3 : ℤ) ^ m ∣ t₀ * (1 + μ + μ ^ 2) * (l - 1) := by
    set e := t₀ * (1 + μ + μ ^ 2) with he
    set f := w₀ * (1 + ν + ν ^ 2) with hf
    have hc : r * (x ^ e * s ^ f) * r⁻¹ = x ^ e * s ^ f := by
      rw [← hcube, (Commute.self_pow r _).eq, mul_inv_cancel_right]
    have hx1 := pow_mul_zpow_mul_inv_pow hrx 1 e
    have hs1 := pow_mul_zpow_mul_inv_pow hrs 1 f
    rw [pow_one, pow_one] at hx1 hs1
    have e2 : r * (x ^ e * s ^ f) * r⁻¹ = (r * x ^ e * r⁻¹) * (r * s ^ f * r⁻¹) := by group
    rw [e2, hx1, hs1] at hc
    have e3 : x ^ (e * l - e) = s ^ (f - f * κ) := by
      rw [zpow_sub, zpow_sub]
      calc x ^ (e * l) * (x ^ e)⁻¹ = (x ^ e)⁻¹ * (x ^ (e * l) * s ^ (f * κ)) *
            (s ^ (f * κ))⁻¹ := by
            group
        _ = s ^ f * (s ^ (f * κ))⁻¹ := by rw [hc]; group
    have := hxs _ _ e3
    rw [hdvd] at this
    have e4 : e * l - e = t₀ * (1 + μ + μ ^ 2) * (l - 1) := by rw [he]; ring
    rwa [e4] at this
  obtain ⟨t, ht⟩ := exists_dvd_mul_add h1 h3 h4 h5
  refine ⟨t, ?_⟩
  have hx0 : x ^ (t * l * ∑ i ∈ Finset.range (3 ^ j), l ^ i + t₀) = 1 := (hdvd _).mpr ht
  rw [zpow_add] at hx0
  rw [mul_zpow_pow_eq hrx, hra]
  calc x ^ (t * l * ∑ i ∈ Finset.range (3 ^ j), l ^ i) * (x ^ t₀ * s ^ w₀ * a)
      = x ^ (t * l * ∑ i ∈ Finset.range (3 ^ j), l ^ i) * x ^ t₀ * s ^ w₀ * a := by group
    _ = s ^ w₀ * a := by rw [hx0, one_mul]
