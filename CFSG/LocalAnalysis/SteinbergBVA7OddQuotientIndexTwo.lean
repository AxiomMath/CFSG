module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo

public section

namespace CFSG.LocalAnalysis.SteinbergBV

open Subgroup

variable {Y : Type*} [Group Y]

theorem odd_orderOf_mem_of_index_eq_two {E : Subgroup Y} (hE : E.index = 2) {y : Y}
    (hy : Odd (orderOf y)) : y ∈ E := by
  have : E.Normal := Subgroup.normal_of_index_eq_two hE
  have hfin : Finite (Y ⧸ E) := Nat.finite_of_card_ne_zero (by rw [← E.index_eq_card, hE]; norm_num)
  have h2 : (y : Y ⧸ E) ^ 2 = 1 := by
    rw [← hE, Subgroup.index_eq_card]
    exact pow_card_eq_one'
  have hodd : (y : Y ⧸ E) ^ orderOf y = 1 := by
    rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have hg := pow_gcd_eq_one.2 ⟨hodd, h2⟩
  rw [(Nat.coprime_two_right.2 hy).gcd_eq_one, pow_one, QuotientGroup.eq_one_iff] at hg
  exact hg

theorem exists_two_pow_mul_odd_decomposition [Finite Y] (d : Y) :
    ∃ u ∈ zpowers d, ∃ v ∈ zpowers d, d = u * v ∧ (∃ k : ℕ, u ^ (2 ^ k) = 1) ∧
      Odd (orderOf v) := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos d).ne'
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)
  have hb := Nat.gcd_eq_gcd_ab (2 ^ k) m
  rw [hcop.gcd_eq_one, Nat.cast_one] at hb
  refine ⟨d ^ ((m : ℤ) * Nat.gcdB (2 ^ k) m), zpow_mem (mem_zpowers d) _,
    d ^ (((2 ^ k : ℕ) : ℤ) * Nat.gcdA (2 ^ k) m), zpow_mem (mem_zpowers d) _, ?_, ⟨k, ?_⟩, ?_⟩
  · rw [← zpow_add, add_comm, ← hb, zpow_one]
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, ← mul_assoc, ← Nat.cast_mul, ← hn, zpow_mul,
      zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · refine Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one ?_)
    rw [← zpow_natCast, ← zpow_mul, mul_comm, ← mul_assoc, ← Nat.cast_mul, mul_comm m, ← hn,
      zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]

theorem normal_two_kernel_odd_quotient_index_two [Finite Y] (P : Subgroup Y) [P.Normal]
    (hP : IsPGroup 2 P) {m : ℕ} (hm : Odd m) (hidx : P.index = 2 * m) (D : Subgroup Y)
    (hD : D = closure ((P : Set Y) ∪ {y | Odd (orderOf y)})) :
    D.Normal ∧ D.index = 2 ∧ P.relIndex D = m ∧ P ≤ D ∧
    (∀ T : Sylow 2 D, (T : Subgroup D) = P.subgroupOf D) ∧
    (∀ d ∈ D, ∃ p ∈ P, ∃ y : Y, Odd (orderOf y) ∧ d = p * y) ∧
    ∀ E : Subgroup Y, P ≤ E → E.index = 2 → E = D := by
  classical
  obtain ⟨k₀, hk₀⟩ := hm
  obtain ⟨D₀, hD₀n, hD₀idx, hPD₀⟩ :=
    GorensteinWalter.exists_normal_index_two_containing_of_index_eq_two_mul_odd
      (N := P) inferInstance ⟨m, hidx⟩ (by rw [hidx, hk₀]; omega)
  have hrel : P.relIndex D₀ = m := by
    have h := Subgroup.relIndex_mul_index hPD₀
    rw [hD₀idx, hidx] at h
    omega
  have hDle : ∀ E : Subgroup Y, P ≤ E → E.index = 2 → D ≤ E := by
    intro E hPE hE
    rw [hD, closure_le]
    rintro y (hy | hy)
    · exact hPE hy
    · exact odd_orderOf_mem_of_index_eq_two hE hy
  have hdecomp : ∀ d ∈ D₀, ∃ p ∈ P, ∃ y : Y, Odd (orderOf y) ∧ d = p * y := by
    intro d hd
    obtain ⟨u, hu, v, -, rfl, ⟨k, hk⟩, hv⟩ := exists_two_pow_mul_odd_decomposition d
    refine ⟨u, ?_, v, hv, rfl⟩
    have huD₀ : u ∈ D₀ := (zpowers_le.2 hd) hu
    have hq : ((⟨u, huD₀⟩ : D₀) : D₀ ⧸ P.subgroupOf D₀) = 1 := by
      have h1 : ((⟨u, huD₀⟩ : D₀) : D₀ ⧸ P.subgroupOf D₀) ^ m = 1 := by
        rw [← hrel, Subgroup.relIndex, Subgroup.index_eq_card]
        exact pow_card_eq_one'
      have h2 : ((⟨u, huD₀⟩ : D₀) : D₀ ⧸ P.subgroupOf D₀) ^ (2 ^ k) = 1 := by
        rw [← QuotientGroup.mk_pow]
        have : (⟨u, huD₀⟩ : D₀) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
        rw [this, QuotientGroup.mk_one]
      have hg := pow_gcd_eq_one.2 ⟨h1, h2⟩
      have hcop : Nat.Coprime m (2 ^ k) :=
        Nat.Coprime.pow_right k (Nat.coprime_two_right.2 ⟨k₀, hk₀⟩)
      rwa [hcop.gcd_eq_one, pow_one] at hg
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at hq
    exact hq
  have hDD₀ : D = D₀ := by
    refine le_antisymm (hDle D₀ hPD₀ hD₀idx) fun d hd => ?_
    obtain ⟨p, hp, y, hy, rfl⟩ := hdecomp d hd
    rw [hD]
    exact mul_mem (subset_closure (Or.inl hp)) (subset_closure (Or.inr hy))
  subst hDD₀
  have hPD : P ≤ D := hPD₀
  refine ⟨hD₀n, hD₀idx, hrel, hPD, fun T => ?_, hdecomp, fun E hPE hE => ?_⟩
  ·
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    have hcardD : Nat.card D = 2 ^ n * m := by
      have h := Subgroup.card_mul_index (P.subgroupOf D)
      rw [Nat.card_congr (subgroupOfEquivOfLe hPD).toEquiv, hn, ← Subgroup.relIndex, hrel] at h
      exact h.symm
    have hfact : (Nat.card D).factorization 2 = n := by
      rw [hcardD, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) (by rw [hk₀]; omega),
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.add_apply, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by rw [hk₀]; omega), add_zero]
    have hS : Nat.card (P.subgroupOf D) = 2 ^ (Nat.card D).factorization 2 := by
      rw [hfact, Nat.card_congr (subgroupOfEquivOfLe hPD).toEquiv, hn]
    set S : Sylow 2 D := Sylow.ofCard (P.subgroupOf D) hS
    have hSn : (S : Subgroup D).Normal := by
      change (P.subgroupOf D).Normal
      infer_instance
    have hU := Sylow.unique_of_normal S hSn
    rw [Subsingleton.elim T S]
    rfl
  ·
    have hle := hDle E hPE hE
    symm
    refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
    have h1 := Subgroup.card_mul_index D
    have h2 := Subgroup.card_mul_index E
    rw [hD₀idx] at h1
    rw [hE] at h2
    omega

end CFSG.LocalAnalysis.SteinbergBV
