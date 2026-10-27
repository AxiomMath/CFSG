module

public import CFSG.Permutation.UnitaryThreeRecognition.StdHyp

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

namespace StdHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f : ℕ} (S : StdHyp G Q a b j s p f 3) [Finite G] [Finite Ω] (h5 : p ^ f = 5)
include S h5

omit [Finite G] [Finite Ω] in
theorem card_torus_eq_eight : Nat.card (pairStab G a b) = 8 := by
  have h := S.hTcard
  rw [mul_comm 2 f, pow_mul, h5] at h
  omega

theorem card_swapFix_eq_two : Nat.card (swapFix G a b s) = 2 := by
  have h := S.root.card_swapFix_mul S.hb S.htwo S.hfaith S.hcomm S.hj S.hj2 S.hj1 S.hsq S.hpp S.hp
    S.hf S.hpodd S.hd S.hQcard S.hΩcard S.hTcard S.hsa S.hs2
  rw [h5] at h
  omega

variable (hcyc : IsCyclic (pairStab G a b))
include hcyc

omit [Finite G] [Finite Ω] in
theorem exists_torus_gen : ∃ t ∈ pairStab G a b, orderOf t = 8 ∧
    ∀ x ∈ pairStab G a b, ∃ k : ℕ, k < 8 ∧ x = t ^ k := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := pairStab G a b)
  have hog : orderOf g = 8 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, S.card_torus_eq_eight h5]
  refine ⟨g, g.2, by rw [Subgroup.orderOf_coe, hog], ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  refine ⟨(n % 8).toNat, ?_, ?_⟩
  · have h1 : n % 8 < 8 := Int.emod_lt_of_pos n (by norm_num)
    have h2 : 0 ≤ n % 8 := Int.emod_nonneg n (by norm_num)
    omega
  · have h2 : 0 ≤ n % 8 := Int.emod_nonneg n (by norm_num)
    have e : g ^ (n % 8).toNat = g ^ n := by
      rw [← zpow_natCast, Int.toNat_of_nonneg h2,
        show (8 : ℤ) = ((orderOf g : ℕ) : ℤ) by rw [hog]; norm_num, zpow_mod_orderOf]
    have := congrArg Subtype.val (e.trans hn)
    simpa using this.symm

variable {t : G} (ht : t ∈ pairStab G a b) (hot : orderOf t = 8)
include ht hot

omit [Finite G] [Finite Ω] h5 hcyc in
theorem pow_four_eq : t ^ 4 = j := by
  have h1 : t ^ 4 * t ^ 4 = 1 := by
    rw [← pow_add, show 4 + 4 = orderOf t by rw [hot], pow_orderOf_eq_one]
  have h2 : t ^ 4 ≠ 1 := by
    intro e
    have := orderOf_le_of_pow_eq_one (by norm_num) e
    omega
  rcases S.hsq _ ((pairStab G a b).pow_mem ht 4) h1 with h | h
  · exact absurd h h2
  · exact h

omit hcyc in
theorem exists_sigma_exponent
    (hgen : ∀ x ∈ pairStab G a b, ∃ k : ℕ, k < 8 ∧ x = t ^ k) :
    ∃ m : ℕ, (m = 3 ∨ m = 7) ∧ s * t * s = t ^ m := by
  have hs : s⁻¹ = s := by rw [inv_eq_iff_mul_eq_one, S.hs2]
  have hsts : s * t * s ∈ pairStab G a b := by
    have := IsRootSubgroup.conj_mem_pairStab S.hsa S.hsb ht
    rwa [hs] at this
  obtain ⟨m, hm8, hm⟩ := hgen _ hsts
  refine ⟨m, ?_, hm⟩
  have hconj : ∀ k : ℕ, s * t ^ k * s = t ^ (m * k) := by
    intro k
    induction k with
    | zero => simp [S.hs2]
    | succ k ih =>
      calc s * t ^ (k + 1) * s = (s * t ^ k * s) * (s * t * s) := by
            rw [pow_succ]
            calc s * (t ^ k * t) * s = s * t ^ k * (s * s) * t * s := by rw [S.hs2]; group
              _ = (s * t ^ k * s) * (s * t * s) := by group
        _ = t ^ (m * (k + 1)) := by rw [ih, hm, ← pow_add]; ring_nf
  have hfixW : ∀ i : ℕ, t ^ (m * i) = t ^ i → t ^ i ∈ swapFix G a b s := by
    intro i hi
    refine mem_swapFix.mpr ⟨(pairStab G a b).pow_mem ht i, ?_⟩
    have := hconj i
    rw [hi] at this
    calc s * t ^ i = s * t ^ i * s * s := by rw [mul_assoc _ s s, S.hs2, mul_one]
      _ = t ^ i * s := by rw [this]
  have hW := S.card_swapFix_eq_two h5
  have three : ∀ x y z : G, x ∈ swapFix G a b s → y ∈ swapFix G a b s → z ∈ swapFix G a b s →
      x ≠ y → x ≠ z → y ≠ z → False := by
    intro x y z hx hy hz hxy hxz hyz
    classical
    have : Fintype (swapFix G a b s) := Fintype.ofFinite _
    have hsub : ({⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩} : Finset (swapFix G a b s)).card ≤
        Fintype.card (swapFix G a b s) := Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton,
      ← Nat.card_eq_fintype_card, hW] at hsub
    · omega
    · simp only [Finset.mem_singleton, Subtype.mk.injEq]; exact hyz
    · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or]
      exact ⟨hxy, hxz⟩
  have hne : ∀ i k : ℕ, i < 8 → k < 8 → i ≠ k → t ^ i ≠ t ^ k := by
    intro i k hi hk hik e
    rw [← hot] at hi hk
    exact hik (pow_injOn_Iio_orderOf hi hk e)
  have ht8 : ∀ n : ℕ, t ^ n = t ^ (n % 8) := by
    intro n; rw [← hot, pow_mod_orderOf]
  interval_cases m
  ·
    exfalso
    have : t = 1 := by
      have e : s * t * s = 1 := by rw [hm, pow_zero]
      calc t = s * (s * t * s) * s := by
            calc t = (s * s) * t * (s * s) := by rw [S.hs2]; group
              _ = s * (s * t * s) * s := by group
        _ = 1 := by rw [e, mul_one, S.hs2]
    rw [this, orderOf_one] at hot; omega
  ·
    exfalso
    have h1 : t ∈ swapFix G a b s := by
      have := hfixW 1 (by rw [one_mul]); rwa [pow_one] at this
    have h2 : t ^ 2 ∈ swapFix G a b s := hfixW 2 (by rw [one_mul])
    have e01 := hne 0 1 (by norm_num) (by norm_num) (by norm_num)
    have e02 := hne 0 2 (by norm_num) (by norm_num) (by norm_num)
    have e12 := hne 1 2 (by norm_num) (by norm_num) (by norm_num)
    rw [pow_zero] at e01 e02
    rw [pow_one] at e01 e12
    exact three 1 t (t ^ 2) (swapFix G a b s).one_mem h1 h2 e01 e02 e12
  ·
    exfalso
    have : t ^ 4 = 1 := by
      have e := hconj 4
      rw [ht8 (2 * 4)] at e
      norm_num at e
      calc t ^ 4 = s * (s * t ^ 4 * s) * s := by
            calc t ^ 4 = (s * s) * t ^ 4 * (s * s) := by rw [S.hs2]; group
              _ = s * (s * t ^ 4 * s) * s := by group
        _ = 1 := by rw [e, mul_one, S.hs2]
    exact hne 4 0 (by norm_num) (by norm_num) (by norm_num) (by simpa using this)
  · exact Or.inl rfl
  ·
    exfalso
    have : t ^ 2 = 1 := by
      have e := hconj 2
      rw [ht8 (4 * 2)] at e
      norm_num at e
      calc t ^ 2 = s * (s * t ^ 2 * s) * s := by
            calc t ^ 2 = (s * s) * t ^ 2 * (s * s) := by rw [S.hs2]; group
              _ = s * (s * t ^ 2 * s) * s := by group
        _ = 1 := by rw [e, mul_one, S.hs2]
    exact hne 2 0 (by norm_num) (by norm_num) (by norm_num) (by simpa using this)
  ·
    exfalso
    exact three (t ^ 2) (t ^ 4) (t ^ 6) (hfixW 2 (by rw [ht8 (5 * 2)]))
      (hfixW 4 (by rw [ht8 (5 * 4)])) (hfixW 6 (by rw [ht8 (5 * 6)]))
      (hne 2 4 (by norm_num) (by norm_num) (by norm_num))
      (hne 2 6 (by norm_num) (by norm_num) (by norm_num))
      (hne 4 6 (by norm_num) (by norm_num) (by norm_num))
  ·
    exfalso
    have : t ^ 4 = 1 := by
      have e := hconj 4
      rw [ht8 (6 * 4)] at e
      norm_num at e
      calc t ^ 4 = s * (s * t ^ 4 * s) * s := by
            calc t ^ 4 = (s * s) * t ^ 4 * (s * s) := by rw [S.hs2]; group
              _ = s * (s * t ^ 4 * s) * s := by group
        _ = 1 := by rw [e, mul_one, S.hs2]
    exact hne 4 0 (by norm_num) (by norm_num) (by norm_num) (by simpa using this)
  · exact Or.inr rfl

end StdHyp

end CFSG.UnitaryThreeRecognition
