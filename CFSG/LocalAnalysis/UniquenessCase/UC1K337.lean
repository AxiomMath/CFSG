module

public import CFSG.Blueprint.Catalog
import CFSG.GH74.KGroups.CoverEven
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearPSU3
import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG.Blueprint (LieModel)

private lemma zmod_eq_one_of_dvd_sub_one {p a : ℕ} (h : p ∣ a - 1) (ha : 1 ≤ a) :
    (a : ZMod p) = 1 := by
  have h0 : ((a - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (a - 1) p).mpr h
  rw [Nat.cast_sub ha, Nat.cast_one, sub_eq_zero] at h0
  exact h0

private lemma zmod_eq_neg_one_of_dvd_add_one {p a : ℕ} (h : p ∣ a + 1) :
    (a : ZMod p) = -1 := by
  have h0 : ((a + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (a + 1) p).mpr h
  rw [Nat.cast_add, Nat.cast_one] at h0
  exact eq_neg_of_add_eq_zero_left h0

private lemma two_pow_eq_one_of_dvd_sub_one {p k : ℕ} (h : p ∣ 2 ^ k - 1) :
    (2 : ZMod p) ^ k = 1 := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h2 := zmod_eq_one_of_dvd_sub_one h h1
  simpa [Nat.cast_pow] using h2

private lemma two_pow_eq_neg_one_of_dvd_add_one {p k : ℕ} (h : p ∣ 2 ^ k + 1) :
    (2 : ZMod p) ^ k = -1 := by
  have h2 := zmod_eq_neg_one_of_dvd_add_one h
  simpa [Nat.cast_pow] using h2

private lemma not_three_dvd_two_pow (a : ℕ) : ¬ (3 : ℕ) ∣ 2 ^ a := by
  intro h
  have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

private lemma two_eq_neg_one_zmod_three : (2 : ZMod 3) = -1 := by
  decide

private lemma orderOf_two_zmod_three : orderOf (2 : ZMod 3) = 2 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 2)]
  refine ⟨by decide, ?_⟩
  intro k hk2 hk0
  interval_cases k
  decide

private lemma two_pow_eq_neg_one_iff {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : ∃ a : ℕ, n = 2 ^ a) :
    ∀ t : ℕ, Odd t →
      ((2 : ZMod p) ^ (t * n) = -1 ↔
        ∃ s : ℕ, s ∣ t ∧ orderOf (2 : ZMod p) = 2 * n * s) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (2 < p) := ⟨by have := hp.two_le; omega⟩
  obtain ⟨a, rfl⟩ := hn
  have hn0 : (0 : ℕ) < 2 ^ a := pow_pos (by norm_num) a
  intro t ht
  have ht_pos : 0 < t := by
    obtain ⟨k, hk⟩ := ht
    omega
  constructor
  · intro h
    have hdvd : orderOf (2 : ZMod p) ∣ 2 ^ (a + 1) * t := by
      have h2 : (2 : ZMod p) ^ (2 ^ (a + 1) * t) = 1 := by
        rw [show 2 ^ (a + 1) * t = (t * 2 ^ a) * 2 by ring, pow_mul, h, neg_one_sq]
      exact orderOf_dvd_iff_pow_eq_one.mpr h2
    have hd0 : orderOf (2 : ZMod p) ≠ 0 := by
      rintro h0
      rw [h0] at hdvd
      obtain ⟨c, hc⟩ := hdvd
      have hpos : 0 < 2 ^ (a + 1) * t :=
        Nat.mul_pos (pow_pos (by norm_num) _) ht_pos
      simp only [zero_mul] at hc
      omega
    obtain ⟨e, u, huodd, hd_eq⟩ := Nat.exists_eq_two_pow_mul_odd hd0
    have hu_dvd : u ∣ t := by
      have hcop : Nat.Coprime u (2 ^ (a + 1)) :=
        (huodd.coprime_two_left.symm).pow_right (a + 1)
      refine hcop.dvd_of_dvd_mul_left ?_
      exact ((hd_eq ▸ dvd_mul_left u (2 ^ e)).trans hdvd)
    have h2e_dvd : 2 ^ e ∣ 2 ^ (a + 1) := by
      have hcop : Nat.Coprime (2 ^ e) t :=
        (ht.coprime_two_left).pow_left e
      refine hcop.dvd_of_dvd_mul_left ?_
      exact mul_comm (2 ^ (a + 1)) t ▸ (hd_eq ▸ dvd_mul_right (2 ^ e) u).trans hdvd
    obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2e_dvd
    have he_le : e ≤ a + 1 := by
      have : e = k := Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) hk_eq
      omega
    have he_eq : e = a + 1 := by
      by_contra hne
      have he_le_a : e ≤ a := by omega
      have hdvd' : orderOf (2 : ZMod p) ∣ t * 2 ^ a := by
        have h1 : 2 ^ e ∣ 2 ^ a := pow_dvd_pow 2 he_le_a
        have h2 : 2 ^ e * u ∣ 2 ^ a * t := Nat.mul_dvd_mul h1 hu_dvd
        exact hd_eq ▸ (mul_comm (2 ^ a) t ▸ h2)
      have h1 : (2 : ZMod p) ^ (t * 2 ^ a) = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp hdvd'
      exact (Ne.symm ZMod.neg_one_ne_one) (h1.symm.trans h)
    refine ⟨u, hu_dvd, ?_⟩
    rw [hd_eq, he_eq]
    ring
  · rintro ⟨s, hs, hd⟩
    obtain ⟨r, ht_eq⟩ := hs
    have hr_odd : Odd r := by
      have hprod : Odd (s * r) := ht_eq ▸ ht
      exact (Nat.odd_mul.mp hprod).2
    have hs_pos : 0 < s := by
      refine Nat.pos_of_dvd_of_pos ⟨r, ht_eq⟩ ht_pos
    have hlt : 2 ^ a * s < orderOf (2 : ZMod p) := by
      rw [hd]
      nlinarith [hn0, hs_pos]
    have hy2 : ((2 : ZMod p) ^ (2 ^ a * s)) ^ 2 = 1 := by
      rw [← pow_mul, show 2 ^ a * s * 2 = 2 * 2 ^ a * s by ring, ← hd,
        pow_orderOf_eq_one]
    have hy_ne_one : (2 : ZMod p) ^ (2 ^ a * s) ≠ 1 :=
      pow_ne_one_of_lt_orderOf (by positivity) hlt
    have hy_neg : (2 : ZMod p) ^ (2 ^ a * s) = -1 := by
      rcases sq_eq_one_iff.mp hy2 with h1 | h1
      · exact absurd h1 hy_ne_one
      · exact h1
    calc (2 : ZMod p) ^ (t * 2 ^ a) = (2 : ZMod p) ^ ((s * r) * 2 ^ a) := by rw [ht_eq]
      _ = ((2 : ZMod p) ^ (2 ^ a * s)) ^ r := by
            rw [show (s * r) * 2 ^ a = (2 ^ a * s) * r by ring, pow_mul]
      _ = (-1) ^ r := by rw [hy_neg]
      _ = -1 := hr_odd.neg_one_pow

private lemma orderOf_eq_two_mul_of_pow_eq_neg_one {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : ∃ a : ℕ, n = 2 ^ a) (h : (2 : ZMod p) ^ n = -1) :
    orderOf (2 : ZMod p) = 2 * n := by
  have hiff := two_pow_eq_neg_one_iff hp hp2 hn 1 (by norm_num : Odd 1)
  have h1 : (2 : ZMod p) ^ (1 * n) = -1 := by simpa using h
  obtain ⟨s, hs, hd⟩ := hiff.mp h1
  have hs1 : s = 1 := Nat.dvd_one.mp hs
  simpa [hs1] using hd

private lemma two_le_of_lieModel_psu3 {X : Type} [Group X] {m : ℕ}
    (h : LieModel X .PSU 3 2 m) : 2 ≤ m := by
  have hadm := h.admissible
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  obtain ⟨-, hm1, -, hmne⟩ := hadm
  have hmne2 : 2 ^ m ≠ 2 := by
    intro h0
    exact hmne (by rw [h0])
  have hm_ne_one : m ≠ 1 := by
    intro h0
    subst h0
    exact hmne2 (by norm_num)
  omega

private lemma two_le_of_lieModel_psl2 {X : Type} [Group X] {m : ℕ}
    (h : LieModel X .PSL 2 2 m) : 2 ≤ m := by
  have hadm := h.admissible
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  obtain ⟨-, hm1, -, hmne, -⟩ := hadm
  have hmne2 : 2 ^ m ≠ 2 := by
    intro h0
    exact hmne (by rw [h0])
  have hm_ne_one : m ≠ 1 := by
    intro h0
    subst h0
    exact hmne2 (by norm_num)
  omega

theorem k337_holds :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ n m : ℕ, (∃ a : ℕ, n = 2 ^ a) → (∃ b : ℕ, m = 2 ^ b) →
      (∀ t : ℕ, Odd t →
        ((2 : ZMod p) ^ (t * n) = -1 ↔ ∃ s : ℕ, s ∣ t ∧ orderOf (2 : ZMod p) = 2 * n * s)) ∧
      ((2 : ZMod p) ^ n = -1 → (2 : ZMod p) ^ m = -1 → n = m) ∧
      ((2 : ZMod p) ^ n = -1 → ∀ (X : Type) [Group X], LieModel X .PSU 3 2 m →
        p ∣ Nat.card X → (2 : ZMod p) ^ (2 * m) = 1) ∧
      ((2 : ZMod p) ^ (3 * n) = -1 → (2 : ZMod p) ^ n ≠ -1 → ∀ (L : Type) [Group L],
        (LieModel L .PSL 2 2 m ∨ LieModel L .PSU 3 2 m) → p ∣ Nat.card L →
          LieModel L .PSU 3 2 n) ∧
      (Odd (orderOf (2 : ZMod p)) → ∀ (X : Type) [Group X], LieModel X .PSU 3 2 n →
        ¬ p ∣ Nat.card X) := by
  intro p hp hp2 n m hn hm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact two_pow_eq_neg_one_iff hp hp2 hn
  · intro h1 h2
    have e1 := orderOf_eq_two_mul_of_pow_eq_neg_one hp hp2 hn h1
    have e2 := orderOf_eq_two_mul_of_pow_eq_neg_one hp hp2 hm h2
    omega
  · intro h1 X _ hX hpdvd
    have hm2 : 2 ≤ m := two_le_of_lieModel_psu3 hX
    by_cases hp3 : p = 3
    · subst hp3
      rw [two_eq_neg_one_zmod_three]
      exact Even.neg_one_pow ⟨m, by ring⟩
    · have hm1 : 1 ≤ m := by omega
      obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even hm2 hX
      have hcard : Nat.card X = Nat.card (CFSG.Open.PSU3 2 m) :=
        Nat.card_congr e.toEquiv
      have hpdvd' : p ∣ Nat.card (CFSG.Open.PSU3 2 m) := hcard ▸ hpdvd
      have hcases :=
        (CFSG.SignalizerFunctorTheorem.CatalogBridge.prime_dvd_card_psu3_iff hm1 hp hp3).mp
          hpdvd'
      rcases hcases with h2m | h2m | h3m
      · have hpdvd2 : p ∣ 2 := hp.dvd_of_dvd_pow h2m
        exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdvd2) hp2
      · exact two_pow_eq_one_of_dvd_sub_one h2m
      · have hneg : (2 : ZMod p) ^ (3 * m) = -1 :=
          two_pow_eq_neg_one_of_dvd_add_one h3m
        have hiff := two_pow_eq_neg_one_iff hp hp2 hm 3 (by norm_num : Odd 3)
        obtain ⟨s, hs, hd⟩ := hiff.mp hneg
        have hd1 := orderOf_eq_two_mul_of_pow_eq_neg_one hp hp2 hn h1
        have h2eq : 2 * n = 2 * (m * s) := by
          calc 2 * n = orderOf (2 : ZMod p) := hd1.symm
            _ = 2 * m * s := hd
            _ = 2 * (m * s) := by ring
        have hnm : n = m * s := Nat.eq_of_mul_eq_mul_left (by norm_num) h2eq
        have hs13 : s = 1 ∨ s = 3 := by
          have := (Nat.dvd_prime Nat.prime_three).mp hs
          tauto
        have hnm' : n = m := by
          rcases hs13 with h1' | h3'
          · subst h1'
            simpa using hnm
          · exfalso
            obtain ⟨a, rfl⟩ := hn
            exact not_three_dvd_two_pow a ⟨m, by rw [hnm, h3']; ring⟩
        have h1m : (2 : ZMod p) ^ m = -1 := by rwa [hnm'] at h1
        rw [show 2 * m = m * 2 by ring, pow_mul, h1m, neg_one_sq]
  · intro h3n hn_neg L _ hL hpdvd
    haveI : Fact p.Prime := ⟨hp⟩
    have hiff3 := two_pow_eq_neg_one_iff hp hp2 hn 3 (by norm_num : Odd 3)
    obtain ⟨s, hs, hd⟩ := hiff3.mp h3n
    have hn_pos : 0 < n := by
      obtain ⟨a, rfl⟩ := hn
      positivity
    have hs13 : s = 1 ∨ s = 3 := by
      have := (Nat.dvd_prime Nat.prime_three).mp hs
      tauto
    have hd6 : orderOf (2 : ZMod p) = 6 * n := by
      rcases hs13 with h1' | h3'
      · exfalso
        subst h1'
        have hd2 : orderOf (2 : ZMod p) = 2 * n := by simpa using hd
        have hy2 : ((2 : ZMod p) ^ n) ^ 2 = 1 := by
          rw [← pow_mul, show n * 2 = 2 * n by ring, ← hd2, pow_orderOf_eq_one]
        have hy_ne_one : (2 : ZMod p) ^ n ≠ 1 :=
          pow_ne_one_of_lt_orderOf (by positivity) (by rw [hd2]; omega)
        have hy_neg : (2 : ZMod p) ^ n = -1 := by
          rcases sq_eq_one_iff.mp hy2 with h1'' | h1''
          · exact absurd h1'' hy_ne_one
          · exact h1''
        exact hn_neg hy_neg
      · subst h3'
        calc orderOf (2 : ZMod p) = 2 * n * 3 := hd
          _ = 6 * n := by ring
    have hp3 : p ≠ 3 := by
      intro hp3eq
      subst hp3eq
      rw [orderOf_two_zmod_three] at hd6
      omega
    rcases hL with hPSL | hPSU
    · exfalso
      have hm2 : 2 ≤ m := two_le_of_lieModel_psl2 hPSL
      obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psl2_of_lieModel_even hm2 hPSL
      have hcard : Nat.card L = Nat.card (CFSG.Theory.Comparator.PSL2Model m) :=
        Nat.card_congr e.toEquiv
      have hpdvd' : p ∣ Nat.card (CFSG.Theory.Comparator.PSL2Model m) := hcard ▸ hpdvd
      rw [CFSG.Theory.Comparator.PSL2Model,
        CFSG.Walter.psl2_even_card (f := m) (by omega)] at hpdvd'
      have hp_not_dvd : ¬ p ∣ 2 ^ m := by
        intro h2
        have h32 : p ∣ 2 := hp.dvd_of_dvd_pow h2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h32)
      have hsq : p ∣ (2 ^ m) ^ 2 - 1 :=
        (hp.dvd_mul.mp hpdvd').resolve_left hp_not_dvd
      have hsq' : p ∣ 2 ^ (2 * m) - 1 := by
        have hcast : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by
          rw [← pow_mul]
          congr 1
          ring
        rwa [hcast] at hsq
      have hpow1 : (2 : ZMod p) ^ (2 * m) = 1 :=
        two_pow_eq_one_of_dvd_sub_one hsq'
      have hdvd : orderOf (2 : ZMod p) ∣ 2 * m :=
        orderOf_dvd_iff_pow_eq_one.mpr hpow1
      have h3dvd2m : 3 ∣ 2 * m := by
        have h3dvd_d : 3 ∣ orderOf (2 : ZMod p) := by
          rw [hd6]
          exact ⟨2 * n, by ring⟩
        exact h3dvd_d.trans hdvd
      have h3m : 3 ∣ m :=
        (Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 3 2) h3dvd2m)
      obtain ⟨b, rfl⟩ := hm
      exact not_three_dvd_two_pow b h3m
    · have hm2 : 2 ≤ m := two_le_of_lieModel_psu3 hPSU
      have hm1 : 1 ≤ m := by omega
      obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even hm2 hPSU
      have hcard : Nat.card L = Nat.card (CFSG.Open.PSU3 2 m) :=
        Nat.card_congr e.toEquiv
      have hpdvd' : p ∣ Nat.card (CFSG.Open.PSU3 2 m) := hcard ▸ hpdvd
      have hcases :=
        (CFSG.SignalizerFunctorTheorem.CatalogBridge.prime_dvd_card_psu3_iff hm1 hp hp3).mp
          hpdvd'
      rcases hcases with h2m | h2m | h3m
      · exfalso
        have hpdvd2 : p ∣ 2 := hp.dvd_of_dvd_pow h2m
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdvd2)
      · exfalso
        have hpow1 : (2 : ZMod p) ^ (2 * m) = 1 :=
          two_pow_eq_one_of_dvd_sub_one h2m
        have hdvd : orderOf (2 : ZMod p) ∣ 2 * m :=
          orderOf_dvd_iff_pow_eq_one.mpr hpow1
        have h3dvd2m : 3 ∣ 2 * m := by
          have h3dvd_d : 3 ∣ orderOf (2 : ZMod p) := by
            rw [hd6]
            exact ⟨2 * n, by ring⟩
          exact h3dvd_d.trans hdvd
        have h3m : 3 ∣ m :=
          (Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 3 2) h3dvd2m)
        obtain ⟨b, rfl⟩ := hm
        exact not_three_dvd_two_pow b h3m
      · have hneg : (2 : ZMod p) ^ (3 * m) = -1 :=
          two_pow_eq_neg_one_of_dvd_add_one h3m
        have hiff := two_pow_eq_neg_one_iff hp hp2 hm 3 (by norm_num : Odd 3)
        obtain ⟨s', hs', hd'⟩ := hiff.mp hneg
        have h2eq' : 2 * (3 * n) = 2 * (m * s') := by
          calc 2 * (3 * n) = 6 * n := by ring
            _ = orderOf (2 : ZMod p) := hd6.symm
            _ = 2 * m * s' := hd'
            _ = 2 * (m * s') := by ring
        have h3n_eq : 3 * n = m * s' := Nat.eq_of_mul_eq_mul_left (by norm_num) h2eq'
        have hs13' : s' = 1 ∨ s' = 3 := by
          have := (Nat.dvd_prime Nat.prime_three).mp hs'
          tauto
        rcases hs13' with h1' | h3'
        · exfalso
          subst h1'
          have h3n_eq' : 3 * n = m := by simpa using h3n_eq
          have h3m : 3 ∣ m := ⟨n, h3n_eq'.symm⟩
          obtain ⟨b, rfl⟩ := hm
          exact not_three_dvd_two_pow b h3m
        · subst h3'
          have hmn : n = m := by omega
          rw [hmn]
          exact hPSU
  · intro hdodd X _ hX hpdvd
    have hn2 : 2 ≤ n := two_le_of_lieModel_psu3 hX
    have hn1 : 1 ≤ n := by omega
    have hp3 : p ≠ 3 := by
      intro hp3eq
      subst hp3eq
      rw [orderOf_two_zmod_three] at hdodd
      exact absurd hdodd (by norm_num)
    obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even hn2 hX
    have hcard : Nat.card X = Nat.card (CFSG.Open.PSU3 2 n) := Nat.card_congr e.toEquiv
    have hpdvd' : p ∣ Nat.card (CFSG.Open.PSU3 2 n) := hcard ▸ hpdvd
    have hcases :=
      (CFSG.SignalizerFunctorTheorem.CatalogBridge.prime_dvd_card_psu3_iff hn1 hp hp3).mp
        hpdvd'
    rcases hcases with h2n | h2n | h3n
    · have hpdvd2 : p ∣ 2 := hp.dvd_of_dvd_pow h2n
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdvd2)
    · exfalso
      have hpow1 : (2 : ZMod p) ^ (2 * n) = 1 :=
        two_pow_eq_one_of_dvd_sub_one h2n
      have hdvd : orderOf (2 : ZMod p) ∣ 2 * n :=
        orderOf_dvd_iff_pow_eq_one.mpr hpow1
      obtain ⟨a, rfl⟩ := hn
      have hdvd' : orderOf (2 : ZMod p) ∣ 2 ^ (a + 1) := by
        have h2 : 2 * 2 ^ a = 2 ^ (a + 1) := by ring
        rwa [h2] at hdvd
      obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
      have hk0 : k = 0 := by
        by_contra hk
        have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
        have heven : Even (2 ^ (j + 1)) := ⟨2 ^ j, by rw [pow_succ]; ring⟩
        have hodd : Odd (orderOf (2 : ZMod p)) := hdodd
        rw [hk_eq] at hodd
        exact (Nat.not_even_iff_odd.mpr hodd) heven
      have hd1 : orderOf (2 : ZMod p) = 1 := by
        rw [hk_eq, hk0]
        norm_num
      have h2one : (2 : ZMod p) = 1 := orderOf_eq_one_iff.mp hd1
      have h10 : (1 : ZMod p) = 0 := by
        have h : (2 : ZMod p) - 1 = 0 := sub_eq_zero.mpr h2one
        rwa [show (2 : ZMod p) - 1 = 1 by ring] at h
      have hp1 : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using h10)
      exact hp.not_dvd_one hp1
    · exfalso
      have hneg : (2 : ZMod p) ^ (3 * n) = -1 :=
        two_pow_eq_neg_one_of_dvd_add_one h3n
      have hiff := two_pow_eq_neg_one_iff hp hp2 hn 3 (by norm_num : Odd 3)
      obtain ⟨s, hs, hd⟩ := hiff.mp hneg
      have heven : Even (orderOf (2 : ZMod p)) := by
        rw [hd]
        exact ⟨n * s, by ring⟩
      exact (Nat.not_even_iff_odd.mpr hdodd) heven

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
