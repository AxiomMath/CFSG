module

public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.GH74.Orders.LieType
public import CFSG.Sporadic.J1
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Timmesfeld CFSG.Timmesfeld.Orders

@[expose] def A38Order (m : ℕ) : Prop :=
  (∃ n, 2 ≤ n ∧ m = ordA 1 (2 ^ n)) ∨ (∃ f, Odd f ∧ 3 ≤ f ∧ m = ordSuzuki (2 ^ f)) ∨
    m = 175560 ∨ ∃ p, p.Prime ∧ 3 < p ∧ m = ordA 1 p

@[expose] def RankTwoOrder (m : ℕ) : Prop :=
  (∃ e, 2 ≤ e ∧ m = ordA 2 (2 ^ e)) ∨ (∃ e, 1 ≤ e ∧ m = ordTwistedA 3 (2 ^ e)) ∨
    (∃ e, 1 ≤ e ∧ m = ordTwistedA 4 (2 ^ e)) ∨ (∃ e, 1 ≤ e ∧ m = ordBC 2 (2 ^ e)) ∨ m = 360 ∨
    (∃ e, 2 ≤ e ∧ m = ordG2 (2 ^ e)) ∨ m = 6048 ∨ (∃ e, 1 ≤ e ∧ m = ordTrialityD4 (2 ^ e)) ∨
    (∃ k, 1 ≤ k ∧ m = ordTwistedF4 (2 ^ (2 * k + 1))) ∨ m = ordTits

theorem ordA_one_two_pow {n : ℕ} (hn : 1 ≤ n) : ordA 1 (2 ^ n) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have h : Nat.gcd 2 (2 ^ n - 1) = 1 := Nat.coprime_two_left.mpr (odd_two_pow_sub_one hn)
  unfold ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton, show (1 + 1 : ℕ) = 2 by rfl, h, Nat.div_one]

theorem two_mul_ordA_one_of_odd {p : ℕ} (hp : Odd p) : 2 * ordA 1 p = p * (p ^ 2 - 1) := by
  have h2 : 2 ∣ p - 1 := by
    obtain ⟨k, rfl⟩ := hp
    exact ⟨k, by omega⟩
  have hdvd : 2 ∣ p * (p ^ 2 - 1) :=
    Dvd.dvd.mul_left (h2.trans (Nat.sub_one_dvd_pow_sub_one p 2)) p
  unfold ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton, show (1 + 1 : ℕ) = 2 by rfl, Nat.gcd_eq_left h2,
    Nat.mul_div_cancel' hdvd]

theorem ordA_two_eq (q : ℕ) :
    ordA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
  unfold ordA
  rw [show 2 * (2 + 1) / 2 = 3 by rfl, show Finset.Icc 2 (2 + 1) = {2, 3} by rfl,
    Finset.prod_pair (by norm_num)]

theorem ordTwistedA_three_eq {q : ℕ} (hq : 1 ≤ q) :
    ordTwistedA 3 q = q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) / Nat.gcd 4 (q + 1) := by
  unfold ordTwistedA
  rw [show 3 * (3 + 1) / 2 = 6 by rfl, show Finset.Icc 2 (3 + 1) = {2, 3, 4} by rfl,
    Finset.prod_insert (by decide), Finset.prod_pair (by norm_num),
    toNat_pow_sub_neg_one_pow_of_even hq (by decide),
    toNat_pow_sub_neg_one_pow_of_odd (by decide), toNat_pow_sub_neg_one_pow_of_even hq (by decide)]
  congr 1
  ring

theorem ordTwistedA_four_eq {q : ℕ} (hq : 1 ≤ q) :
    ordTwistedA 4 q =
      q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1)) / Nat.gcd 5 (q + 1) := by
  unfold ordTwistedA
  rw [show 4 * (4 + 1) / 2 = 10 by rfl, show Finset.Icc 2 (4 + 1) = {2, 3, 4, 5} by rfl,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by norm_num),
    toNat_pow_sub_neg_one_pow_of_even hq (by decide),
    toNat_pow_sub_neg_one_pow_of_odd (by decide), toNat_pow_sub_neg_one_pow_of_even hq (by decide),
    toNat_pow_sub_neg_one_pow_of_odd (by decide)]
  congr 1
  ring

theorem ordBC_two_two_pow {e : ℕ} (he : 1 ≤ e) :
    ordBC 2 (2 ^ e) = (2 ^ e) ^ 4 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 4 - 1)) := by
  have h : Nat.gcd 2 (2 ^ e - 1) = 1 := Nat.coprime_two_left.mpr (odd_two_pow_sub_one he)
  unfold ordBC
  rw [h, Nat.div_one, show 2 * 2 = 4 by rfl, show Finset.Icc 1 2 = {1, 2} by rfl,
    Finset.prod_pair (by norm_num)]

theorem two_part_ordA_one {n : ℕ} (hn : 1 ≤ n) : ∃ r, Odd r ∧ ordA 1 (2 ^ n) = 2 ^ n * r :=
  ⟨_, by rw [← pow_mul]; exact odd_two_pow_sub_one (by omega), ordA_one_two_pow hn⟩

theorem two_part_ordSuzuki {f : ℕ} (hf : 1 ≤ f) :
    ∃ r, Odd r ∧ ordSuzuki (2 ^ f) = 2 ^ (f * 2) * r :=
  (profile_ordSuzuki hf).two

theorem two_part_ordA_two {e : ℕ} (he : 1 ≤ e) : ∃ r, Odd r ∧ ordA 2 (2 ^ e) = 2 ^ (e * 3) * r :=
  (profile_ordA (n := 2) (by norm_num) he).two

theorem two_part_ordTwistedA_three {e : ℕ} (he : 1 ≤ e) :
    ∃ r, Odd r ∧ ordTwistedA 3 (2 ^ e) = 2 ^ (e * 6) * r :=
  (profile_ordTwistedA (n := 3) (by norm_num) he).two

theorem two_part_ordTwistedA_four {e : ℕ} (he : 1 ≤ e) :
    ∃ r, Odd r ∧ ordTwistedA 4 (2 ^ e) = 2 ^ (e * 10) * r :=
  (profile_ordTwistedA (n := 4) (by norm_num) he).two

theorem two_part_ordBC_two {e : ℕ} (he : 1 ≤ e) : ∃ r, Odd r ∧ ordBC 2 (2 ^ e) = 2 ^ (e * 4) * r :=
  (profile_ordBC (n := 2) he).two

theorem two_part_ordG2 {e : ℕ} (he : 1 ≤ e) : ∃ r, Odd r ∧ ordG2 (2 ^ e) = 2 ^ (e * 6) * r :=
  (profile_ordG2 he).two

theorem two_part_ordTrialityD4 {e : ℕ} (he : 1 ≤ e) :
    ∃ r, Odd r ∧ ordTrialityD4 (2 ^ e) = 2 ^ (e * 12) * r :=
  (profile_ordTrialityD4 he).two

theorem two_part_ordTwistedF4 {f : ℕ} (hf : 1 ≤ f) :
    ∃ r, Odd r ∧ ordTwistedF4 (2 ^ f) = 2 ^ (f * 12) * r :=
  (profile_ordTwistedF4 hf).two

theorem ne_of_two_part {m m' N N' : ℕ} (h : ∃ r, Odd r ∧ m = 2 ^ N * r)
    (h' : ∃ r, Odd r ∧ m' = 2 ^ N' * r) (hne : N ≠ N') : m ≠ m' := by
  rintro rfl
  obtain ⟨r, hr, hm⟩ := h
  obtain ⟨r', hr', hm'⟩ := h'
  exact hne (eq_of_two_pow_mul_odd hr hr' (hm.symm.trans hm'))

theorem prim_not_dvd_two_pow {p k : ℕ} (hp : IsPrimitivePrimeDivisor p k) (hk : 0 < k) (a : ℕ) :
    ¬ p ∣ 2 ^ a := fun h =>
  hp.ne_two hk ((Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).1 (hp.prime.dvd_of_dvd_pow h))

theorem prim_not_dvd_sub_one {p k : ℕ} (hp : IsPrimitivePrimeDivisor p k) (hk : 0 < k)
    {e i : ℕ} (hei : 0 < e * i) (hlt : e * i < k) : ¬ p ∣ (2 ^ e) ^ i - 1 := fun h =>
  Nat.not_dvd_of_pos_of_lt hei hlt ((PrimDiv.dvd_pow_sub_one_iff hp hk e i).1 h)

theorem prim_not_dvd_add_one {p k : ℕ} (hp : IsPrimitivePrimeDivisor p k) (hk : 0 < k)
    {e i : ℕ} (hei : 0 < e * i) (hlt : 2 * (e * i) < k) : ¬ p ∣ (2 ^ e) ^ i + 1 := fun h =>
  Nat.not_dvd_of_pos_of_lt (by omega) hlt ((PrimDiv.dvd_pow_add_one_iff hp hk e i).1 h).1

theorem exists_prim_dvd_ordA_one {n : ℕ} (hn : 1 ≤ n) (hn3 : n ≠ 3) :
    ∃ p, IsPrimitivePrimeDivisor p (2 * n) ∧ p ∣ ordA 1 (2 ^ n) := by
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 2 * n) (by omega) (by omega)
  refine ⟨p, hp, ?_⟩
  rw [ordA_one_two_pow hn, ← pow_mul, mul_comm n 2]
  exact dvd_mul_of_dvd_right hp.dvd _

theorem exists_prim_dvd_ordSuzuki {f : ℕ} (hf : 1 ≤ f) :
    ∃ p, IsPrimitivePrimeDivisor p (2 * (f * 2)) ∧ p ∣ ordSuzuki (2 ^ f) := by
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 2 * (f * 2)) (by omega) (by omega)
  refine ⟨p, hp, ?_⟩
  have h : p ∣ (2 ^ f) ^ 2 + 1 := by
    rw [← pow_mul, hp.dvd_add_one_iff (by omega)]
    exact ⟨dvd_rfl, Nat.not_dvd_of_pos_of_lt (by omega) (by omega)⟩
  unfold ordSuzuki
  exact Dvd.dvd.mul_right (dvd_mul_of_dvd_right h _) _

theorem prim_not_dvd_ordA_two {e p k : ℕ} (he : 1 ≤ e) (hp : IsPrimitivePrimeDivisor p k)
    (hk : e * 3 < k) : ¬ p ∣ ordA 2 (2 ^ e) := by
  intro h
  have hk0 : 0 < k := by omega
  rw [ordA_two_eq] at h
  have hd : Nat.gcd 3 (2 ^ e - 1) ∣ (2 ^ e) ^ 3 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 - 1)) :=
    (Nat.gcd_dvd_right _ _).trans (Dvd.dvd.mul_left (Dvd.dvd.mul_right
      (by simpa using Nat.sub_one_dvd_pow_sub_one (2 ^ e) 2) _) _)
  have h' := h.trans (Nat.div_dvd_of_dvd hd)
  rcases hp.prime.dvd_mul.1 h' with h1 | h1
  · exact prim_not_dvd_two_pow hp hk0 (e * 3) (by rwa [pow_mul])
  rcases hp.prime.dvd_mul.1 h1 with h2 | h2
  · exact prim_not_dvd_sub_one hp hk0 (by positivity) (by omega) h2
  · exact prim_not_dvd_sub_one hp hk0 (by positivity) (by omega) h2

theorem prim_not_dvd_ordG2 {e p k : ℕ} (he : 1 ≤ e) (hp : IsPrimitivePrimeDivisor p k)
    (hk : e * 6 < k) : ¬ p ∣ ordG2 (2 ^ e) := by
  intro h
  have hk0 : 0 < k := by omega
  rw [ordG2_eq] at h
  rcases hp.prime.dvd_mul.1 h with h1 | h1
  · exact prim_not_dvd_two_pow hp hk0 _ h1
  rcases hp.prime.dvd_mul.1 h1 with h2 | h2
  · exact prim_not_dvd_sub_one hp hk0 (by positivity) (by omega) h2
  · exact prim_not_dvd_sub_one hp hk0 (by positivity) (by omega) h2

theorem prim_not_dvd_ordTrialityD4 {e p k : ℕ} (he : 1 ≤ e) (hp : IsPrimitivePrimeDivisor p k)
    (hk : e * 12 < k) : ¬ p ∣ ordTrialityD4 (2 ^ e) := by
  intro h
  have hk0 : 0 < k := by omega
  have h12 : (2 ^ e) ^ 8 + (2 ^ e) ^ 4 + 1 ∣ (2 ^ e) ^ 12 - 1 := by
    refine ⟨(2 ^ e) ^ 4 - 1, ?_⟩
    have h1 : 1 ≤ (2 ^ e) ^ 4 := Nat.one_le_pow _ _ (by positivity)
    have h2 : 1 ≤ (2 ^ e) ^ 12 := Nat.one_le_pow _ _ (by positivity)
    zify [h1, h2]
    ring
  unfold ordTrialityD4 at h
  rcases hp.prime.dvd_mul.1 h with h1 | h1
  · rcases hp.prime.dvd_mul.1 h1 with h2 | h2
    · rcases hp.prime.dvd_mul.1 h2 with h3 | h3
      · exact prim_not_dvd_two_pow hp hk0 (e * 12) (by rwa [pow_mul])
      · exact prim_not_dvd_sub_one hp hk0 (by positivity) (by omega) (h3.trans h12)
    · exact prim_not_dvd_sub_one hp hk0 (by positivity) (by omega) h2
  · exact prim_not_dvd_sub_one hp hk0 (by positivity) (by omega) h1

theorem prim_not_dvd_ordTwistedF4 {f p k : ℕ} (hf : 1 ≤ f) (hp : IsPrimitivePrimeDivisor p k)
    (hk : f * 12 < k) : ¬ p ∣ ordTwistedF4 (2 ^ f) := by
  intro h
  have hk0 : 0 < k := by omega
  unfold ordTwistedF4 at h
  rcases hp.prime.dvd_mul.1 h with h1 | h1
  · rcases hp.prime.dvd_mul.1 h1 with h2 | h2
    · rcases hp.prime.dvd_mul.1 h2 with h3 | h3
      · rcases hp.prime.dvd_mul.1 h3 with h4 | h4
        · exact prim_not_dvd_two_pow hp hk0 (f * 12) (by rwa [pow_mul])
        · exact prim_not_dvd_add_one hp hk0 (by positivity) (by omega) h4
      · exact prim_not_dvd_sub_one hp hk0 (by positivity) (by omega) h3
    · exact prim_not_dvd_add_one hp hk0 (by positivity) (by omega) h2
  · exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) ((hp.dvd_sub_one_iff hk0 f).1 h1)

theorem ne_of_two_part_prim {m m' N N' : ℕ} (h : ∃ r, Odd r ∧ m = 2 ^ N * r)
    (h' : ∃ r, Odd r ∧ m' = 2 ^ N' * r) (hN' : 1 ≤ N') (h3 : N' ≠ 3)
    (hprim : N ≠ 3 → ∃ p, IsPrimitivePrimeDivisor p (2 * N) ∧ p ∣ m)
    (hnot : ∀ p k, IsPrimitivePrimeDivisor p k → N' < k → ¬ p ∣ m') : m ≠ m' := by
  intro hm
  obtain ⟨r, hr, hmr⟩ := h
  obtain ⟨r', hr', hmr'⟩ := h'
  have hNN : N = N' := eq_of_two_pow_mul_odd hr hr' (hmr.symm.trans (hm.trans hmr'))
  subst hNN
  obtain ⟨p, hp, hpm⟩ := hprim h3
  exact hnot p _ hp (by omega) (hm ▸ hpm)

theorem two_pow_le_of_dvd_ordA_one {p N : ℕ} (hp : Odd p) (hp3 : 3 ≤ p)
    (h : 2 ^ N ∣ ordA 1 p) : 2 ^ N ≤ p + 1 := by
  obtain ⟨a, rfl⟩ := hp
  rcases N with _ | N
  · simp
  have h2 := two_mul_ordA_one_of_odd ⟨a, rfl⟩
  have hsq : (2 * a + 1) ^ 2 - 1 = 2 * 2 * (a * (a + 1)) := by
    have : (2 * a + 1) ^ 2 = 2 * 2 * (a * (a + 1)) + 1 := by ring
    omega
  have hord : ordA 1 (2 * a + 1) = 2 * ((2 * a + 1) * (a * (a + 1))) := by
    rw [hsq] at h2
    have : 2 * ordA 1 (2 * a + 1) = 2 * (2 * ((2 * a + 1) * (a * (a + 1)))) := by
      rw [h2]
      ring
    omega
  rw [hord, pow_succ, mul_comm (2 ^ N) 2] at h
  have h1 : 2 ^ N ∣ (2 * a + 1) * (a * (a + 1)) := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  have hc : Nat.Coprime (2 ^ N) (2 * a + 1) :=
    Nat.Coprime.pow_left N (Nat.coprime_two_left.mpr ⟨a, rfl⟩)
  have h1' : 2 ^ N ∣ a * (a + 1) := hc.dvd_of_dvd_mul_left h1
  have hle : 2 ^ N ≤ a + 1 := by
    rcases Nat.even_or_odd a with ha | ha
    · have hc' : Nat.Coprime (2 ^ N) (a + 1) :=
        Nat.Coprime.pow_left N (Nat.coprime_two_left.mpr ha.add_one)
      have := Nat.le_of_dvd (by omega) (hc'.dvd_of_dvd_mul_right h1')
      omega
    · have hc' : Nat.Coprime (2 ^ N) a := Nat.Coprime.pow_left N (Nat.coprime_two_left.mpr ha)
      exact Nat.le_of_dvd (by omega) (hc'.dvd_of_dvd_mul_left h1')
  rw [pow_succ]
  omega

theorem ordA_one_ge {p M : ℕ} (hp : Odd p) (hM : M ≤ p + 1) :
    (M - 1) * ((M - 1) ^ 2 - 1) ≤ 2 * ordA 1 p := by
  rw [two_mul_ordA_one_of_odd hp]
  have h1 : M - 1 ≤ p := by omega
  exact Nat.mul_le_mul h1 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h1 2) 1)

theorem ordA_one_ne_of_two_pow {p b N : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hdvd : 2 ^ N ∣ b)
    (hlt : 2 * b < (2 ^ N - 1) * ((2 ^ N - 1) ^ 2 - 1)) : ordA 1 p ≠ b := by
  rintro rfl
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have := ordA_one_ge hodd (two_pow_le_of_dvd_ordA_one hodd (by omega) hdvd)
  omega

theorem two_mul_lt_of_le {b M c : ℕ} (hb : b ≤ M * ((M - 1) * c)) (hc : 2 * c + 2 < M) :
    2 * b < (M - 1) * ((M - 1) ^ 2 - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
  have hM : (k + 2 - 1) ^ 2 - 1 = (k + 2) * k := by
    rw [show k + 2 - 1 = k + 1 by omega]
    have : (k + 1) ^ 2 = (k + 2) * k + 1 := by ring
    omega
  rw [hM]
  calc 2 * b ≤ 2 * ((k + 2) * ((k + 2 - 1) * c)) := Nat.mul_le_mul_left 2 hb
    _ = (k + 2 - 1) * ((k + 2) * (2 * c)) := by ring
    _ < (k + 2 - 1) * ((k + 2) * k) :=
        Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left (by omega) (by omega)) (by omega)

theorem two_mul_pow_add_two_lt {q k m : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) (hkm : k + 2 ≤ m) :
    2 * q ^ k + 2 < q ^ m := by
  have h1 : q ^ k * q ^ 2 ≤ q ^ m := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by omega) hkm
  have h2 : 4 ≤ q ^ 2 := by nlinarith
  have h3 : 2 ≤ q ^ k := le_trans hq (Nat.le_self_pow (by omega) q)
  nlinarith

theorem two_le_two_pow {e : ℕ} (he : 1 ≤ e) : 2 ≤ 2 ^ e := Nat.one_lt_two_pow (by omega)

theorem ordA_two_small {e : ℕ} (he : 2 ≤ e) :
    2 * ordA 2 (2 ^ e) < (2 ^ (e * 3) - 1) * ((2 ^ (e * 3) - 1) ^ 2 - 1) := by
  rw [pow_mul]
  have hq4 : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  generalize 2 ^ e = q at hq4 ⊢
  refine two_mul_lt_of_le (c := q ^ 2) ?_ ?_
  · calc ordA 2 q ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
          rw [ordA_two_eq]
          exact Nat.div_le_self _ _
      _ ≤ q ^ 3 * ((q ^ 3 - 1) * q ^ 2) := by
          rw [mul_comm (q ^ 2 - 1)]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  · have h1 : q ^ 2 * 4 ≤ q ^ 3 := by
      rw [pow_succ]
      exact Nat.mul_le_mul_left _ hq4
    have h2 : 16 ≤ q ^ 2 := by nlinarith
    omega

theorem ordTwistedA_three_small {e : ℕ} (he : 1 ≤ e) :
    2 * ordTwistedA 3 (2 ^ e) < (2 ^ (e * 6) - 1) * ((2 ^ (e * 6) - 1) ^ 2 - 1) := by
  rw [pow_mul]
  have hq2 := two_le_two_pow he
  generalize 2 ^ e = q at hq2 ⊢
  have hq1 : 1 ≤ q := by omega
  refine two_mul_lt_of_le (c := q ^ 4) ?_ (two_mul_pow_add_two_lt hq2 (by norm_num) le_rfl)
  have h1 : (q ^ 2 - 1) * (q ^ 3 + 1) ≤ q ^ 6 - 1 := by
    have a1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
    have a2 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq1
    have b1 : (q : ℤ) ^ 5 ≤ (q : ℤ) ^ 6 := by exact_mod_cast Nat.pow_le_pow_right hq1 (by norm_num)
    have b2 : (q : ℤ) ^ 2 ≤ (q : ℤ) ^ 3 := by exact_mod_cast Nat.pow_le_pow_right hq1 (by norm_num)
    zify [a1, a2]
    nlinarith
  calc ordTwistedA 3 q ≤ q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) := by
        rw [ordTwistedA_three_eq hq1]
        exact Nat.div_le_self _ _
    _ ≤ q ^ 6 * ((q ^ 6 - 1) * q ^ 4) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 (Nat.sub_le _ _))

theorem ordTwistedA_four_small {e : ℕ} (he : 1 ≤ e) :
    2 * ordTwistedA 4 (2 ^ e) < (2 ^ (e * 10) - 1) * ((2 ^ (e * 10) - 1) ^ 2 - 1) := by
  rw [pow_mul]
  have hq2 := two_le_two_pow he
  generalize 2 ^ e = q at hq2 ⊢
  have hq1 : 1 ≤ q := by omega
  refine two_mul_lt_of_le (c := q ^ 5) ?_ (two_mul_pow_add_two_lt hq2 (by norm_num) (by norm_num))
  have a2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have a5 : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ hq1
  have a10 : 1 ≤ q ^ 10 := Nat.one_le_pow _ _ hq1
  have h1 : (q ^ 2 - 1) * (q ^ 3 + 1) ≤ q ^ 5 := by
    have b2 : (q : ℤ) ^ 2 ≤ (q : ℤ) ^ 3 := by exact_mod_cast Nat.pow_le_pow_right hq1 (by norm_num)
    zify [a2]
    nlinarith
  have h2 : q ^ 4 - 1 ≤ q ^ 5 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_right hq1 (by norm_num)) 1
  have h3 : (q ^ 5 - 1) * (q ^ 5 + 1) = q ^ 10 - 1 := by
    zify [a5, a10]
    ring
  calc ordTwistedA 4 q ≤ q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1)) := by
        rw [ordTwistedA_four_eq hq1]
        exact Nat.div_le_self _ _
    _ ≤ q ^ 10 * (q ^ 5 * (q ^ 5 - 1) * (q ^ 5 + 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 h2))
    _ = q ^ 10 * ((q ^ 10 - 1) * q ^ 5) := by rw [← h3]; ring

theorem ordBC_two_small {e : ℕ} (he : 1 ≤ e) :
    2 * ordBC 2 (2 ^ e) < (2 ^ (e * 4) - 1) * ((2 ^ (e * 4) - 1) ^ 2 - 1) := by
  rw [ordBC_two_two_pow he, pow_mul]
  have hq2 := two_le_two_pow he
  generalize 2 ^ e = q at hq2 ⊢
  refine two_mul_lt_of_le (c := q ^ 2) ?_ (two_mul_pow_add_two_lt hq2 (by norm_num) le_rfl)
  rw [mul_comm (q ^ 2 - 1)]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

theorem ordG2_small {e : ℕ} (he : 1 ≤ e) :
    2 * ordG2 (2 ^ e) < (2 ^ (e * 6) - 1) * ((2 ^ (e * 6) - 1) ^ 2 - 1) := by
  rw [ordG2_eq, pow_mul]
  have hq2 := two_le_two_pow he
  generalize 2 ^ e = q at hq2 ⊢
  exact two_mul_lt_of_le (c := q ^ 2)
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _)))
    (two_mul_pow_add_two_lt hq2 (by norm_num) (by norm_num))

theorem ordTrialityD4_small {e : ℕ} (he : 1 ≤ e) :
    2 * ordTrialityD4 (2 ^ e) < (2 ^ (e * 12) - 1) * ((2 ^ (e * 12) - 1) ^ 2 - 1) := by
  rw [pow_mul]
  have hq2 := two_le_two_pow he
  generalize 2 ^ e = q at hq2 ⊢
  refine two_mul_lt_of_le (c := q ^ 8) ?_ (two_mul_pow_add_two_lt hq2 (by norm_num) (by norm_num))
  have a12 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ (by omega)
  have h1 : q ^ 8 + q ^ 4 + 1 ≤ q ^ 12 - 1 := by
    have b1 : q ^ 4 * q ^ 8 = q ^ 12 := by ring
    have b2 : 16 ≤ q ^ 4 := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq2 4
    have b3 : q ^ 4 ≤ q ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have b4 : 16 * q ^ 8 ≤ q ^ 12 := by rw [← b1]; exact Nat.mul_le_mul_right _ b2
    omega
  have h2 : (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 8 :=
    calc (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 6 * q ^ 2 :=
          Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
      _ = q ^ 8 := by ring
  calc ordTrialityD4 q = q ^ 12 * ((q ^ 8 + q ^ 4 + 1) * ((q ^ 6 - 1) * (q ^ 2 - 1))) := by
        unfold ordTrialityD4
        ring
    _ ≤ q ^ 12 * ((q ^ 12 - 1) * q ^ 8) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2)

theorem ordTwistedF4_small {f : ℕ} (hf : 1 ≤ f) :
    2 * ordTwistedF4 (2 ^ f) < (2 ^ (f * 12) - 1) * ((2 ^ (f * 12) - 1) ^ 2 - 1) := by
  rw [pow_mul]
  have hq2 := two_le_two_pow hf
  generalize 2 ^ f = q at hq2 ⊢
  have hq1 : 1 ≤ q := by omega
  refine two_mul_lt_of_le (c := q ^ 3) ?_ (two_mul_pow_add_two_lt hq2 (by norm_num) (by norm_num))
  have a4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq1
  have a6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq1
  have a12 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ hq1
  have h1 : (q ^ 3 + 1) * (q - 1) ≤ q ^ 4 := by
    have b1 : (q : ℤ) ≤ (q : ℤ) ^ 3 := by exact_mod_cast Nat.le_self_pow (by norm_num) q
    zify [hq1]
    nlinarith
  have h2 : (q ^ 4 - 1) * q ^ 4 ≤ (q ^ 6 - 1) * q ^ 3 := by
    have b1 : (q : ℤ) ^ 8 ≤ (q : ℤ) ^ 9 := by exact_mod_cast Nat.pow_le_pow_right hq1 (by norm_num)
    have b2 : (q : ℤ) ^ 3 ≤ (q : ℤ) ^ 4 := by exact_mod_cast Nat.pow_le_pow_right hq1 (by norm_num)
    zify [a4, a6]
    nlinarith
  have h3 : (q ^ 6 + 1) * (q ^ 6 - 1) = q ^ 12 - 1 := by
    zify [a6, a12]
    ring
  calc ordTwistedF4 q = q ^ 12 * ((q ^ 6 + 1) * ((q ^ 4 - 1) * ((q ^ 3 + 1) * (q - 1)))) := by
        unfold ordTwistedF4
        ring
    _ ≤ q ^ 12 * ((q ^ 6 + 1) * ((q ^ 4 - 1) * q ^ 4)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1))
    _ ≤ q ^ 12 * ((q ^ 6 + 1) * ((q ^ 6 - 1) * q ^ 3)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
    _ = q ^ 12 * ((q ^ 12 - 1) * q ^ 3) := by rw [← h3]; ring

theorem ordA_one_two_pow_not_rankTwoOrder {n : ℕ} (hn : 2 ≤ n) :
    ¬ RankTwoOrder (ordA 1 (2 ^ n)) := by
  have hm := two_part_ordA_one (n := n) (by omega)
  have hprim : n ≠ 3 → ∃ p, IsPrimitivePrimeDivisor p (2 * n) ∧ p ∣ ordA 1 (2 ^ n) :=
    exists_prim_dvd_ordA_one (by omega)
  rintro (⟨e, he, h⟩ | ⟨e, he, h⟩ | ⟨e, he, h⟩ | ⟨e, he, h⟩ | h | ⟨e, he, h⟩ | h | ⟨e, he, h⟩ |
    ⟨k, hk, h⟩ | h)
  · exact ne_of_two_part_prim hm (two_part_ordA_two (by omega)) (by omega) (by omega) hprim
      (fun p k hp hk => prim_not_dvd_ordA_two (by omega) hp hk) h
  · exact ordA_ne_ordTwistedA le_rfl (by omega) (by norm_num) he h
  · exact ordA_ne_ordTwistedA le_rfl (by omega) (by norm_num) he h
  · exact ordA_ne_ordBC_two le_rfl (by omega) he h
  · by_cases h3 : n = 3
    · subst h3
      revert h
      decide +kernel
    · exact ne_of_two_part hm ⟨45, by decide, by norm_num⟩ h3 h
  · exact ne_of_two_part_prim hm (two_part_ordG2 (by omega)) (by omega) (by omega) hprim
      (fun p k hp hk => prim_not_dvd_ordG2 (by omega) hp hk) h
  · by_cases h5 : n = 5
    · subst h5
      revert h
      decide +kernel
    · exact ne_of_two_part hm ⟨189, by decide, by norm_num⟩ h5 h
  · exact ne_of_two_part_prim hm (two_part_ordTrialityD4 he) (by omega) (by omega) hprim
      (fun p k hp hk => prim_not_dvd_ordTrialityD4 he hp hk) h
  · exact ne_of_two_part_prim hm (two_part_ordTwistedF4 (by omega)) (by omega) (by omega) hprim
      (fun p k hp hk => prim_not_dvd_ordTwistedF4 (by omega) hp hk) h
  · by_cases h11 : n = 11
    · subst h11
      revert h
      decide +kernel
    · exact ne_of_two_part hm ⟨8775, by decide, ordTits_eq⟩ h11 h

theorem ordSuzuki_not_rankTwoOrder {f : ℕ} (hf : Odd f) (hf3 : 3 ≤ f) :
    ¬ RankTwoOrder (ordSuzuki (2 ^ f)) := by
  have hm := two_part_ordSuzuki (f := f) (by omega)
  have hprim : f * 2 ≠ 3 →
      ∃ p, IsPrimitivePrimeDivisor p (2 * (f * 2)) ∧ p ∣ ordSuzuki (2 ^ f) :=
    fun _ => exists_prim_dvd_ordSuzuki (by omega)
  rintro (⟨e, he, h⟩ | ⟨e, he, h⟩ | ⟨e, he, h⟩ | ⟨e, he, h⟩ | h | ⟨e, he, h⟩ | h | ⟨e, he, h⟩ |
    ⟨k, hk, h⟩ | h)
  · exact ne_of_two_part_prim hm (two_part_ordA_two (by omega)) (by omega) (by omega) hprim
      (fun p k hp hk => prim_not_dvd_ordA_two (by omega) hp hk) h
  · exact ordSuzuki_ne_ordTwistedA hf hf3 (by norm_num) he h
  · exact ordSuzuki_ne_ordTwistedA hf hf3 (by norm_num) he h
  · exact ordSuzuki_ne_ordBC_two hf he h
  · exact ne_of_two_part (N' := 3) hm ⟨45, by decide, by norm_num⟩ (by omega) h
  · exact ne_of_two_part_prim hm (two_part_ordG2 (by omega)) (by omega) (by omega) hprim
      (fun p k hp hk => prim_not_dvd_ordG2 (by omega) hp hk) h
  · exact ne_of_two_part (N' := 5) hm ⟨189, by decide, by norm_num⟩ (by omega) h
  · exact ne_of_two_part_prim hm (two_part_ordTrialityD4 he) (by omega) (by omega) hprim
      (fun p k hp hk => prim_not_dvd_ordTrialityD4 he hp hk) h
  · exact ne_of_two_part_prim hm (two_part_ordTwistedF4 (by omega)) (by omega) (by omega) hprim
      (fun p k hp hk => prim_not_dvd_ordTwistedF4 (by omega) hp hk) h
  · exact ne_of_two_part hm ⟨8775, by decide, ordTits_eq⟩ (by omega) h

theorem j1_not_rankTwoOrder : ¬ RankTwoOrder 175560 := by
  have hm : ∃ r, Odd r ∧ 175560 = 2 ^ 3 * r := ⟨21945, by decide, by norm_num⟩
  rintro (⟨e, he, h⟩ | ⟨e, he, h⟩ | ⟨e, he, h⟩ | ⟨e, he, h⟩ | h | ⟨e, he, h⟩ | h | ⟨e, he, h⟩ |
    ⟨k, hk, h⟩ | h)
  · exact ne_of_two_part hm (two_part_ordA_two (by omega)) (by omega) h
  · exact ne_of_two_part hm (two_part_ordTwistedA_three he) (by omega) h
  · exact ne_of_two_part hm (two_part_ordTwistedA_four he) (by omega) h
  · exact ne_of_two_part hm (two_part_ordBC_two he) (by omega) h
  · norm_num at h
  · exact ne_of_two_part hm (two_part_ordG2 (by omega)) (by omega) h
  · norm_num at h
  · exact ne_of_two_part hm (two_part_ordTrialityD4 he) (by omega) h
  · exact ne_of_two_part hm (two_part_ordTwistedF4 (by omega)) (by omega) h
  · rw [ordTits_eq] at h
    norm_num at h

theorem ordA_one_prime_not_rankTwoOrder {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ¬ RankTwoOrder (ordA 1 p) := by
  have key : ∀ {b N : ℕ}, (∃ r, Odd r ∧ b = 2 ^ N * r) →
      2 * b < (2 ^ N - 1) * ((2 ^ N - 1) ^ 2 - 1) → ordA 1 p ≠ b :=
    fun ⟨r, _, hr⟩ hlt => ordA_one_ne_of_two_pow hp hp3 ⟨r, hr⟩ hlt
  rintro (⟨e, he, h⟩ | ⟨e, he, h⟩ | ⟨e, he, h⟩ | ⟨e, he, h⟩ | h | ⟨e, he, h⟩ | h | ⟨e, he, h⟩ |
    ⟨k, hk, h⟩ | h)
  · exact key (two_part_ordA_two (by omega)) (ordA_two_small he) h
  · exact key (two_part_ordTwistedA_three he) (ordTwistedA_three_small he) h
  · exact key (two_part_ordTwistedA_four he) (ordTwistedA_four_small he) h
  · exact key (two_part_ordBC_two he) (ordBC_two_small he) h
  ·
    have h2 := two_mul_ordA_one_of_odd (hp.odd_of_ne_two (by omega))
    rw [h] at h2
    have hp10 : p < 10 := by
      by_contra hc
      have h10 : 10 ≤ p := by omega
      have : 10 * 99 ≤ p * (p ^ 2 - 1) :=
        Nat.mul_le_mul h10 (by have := Nat.pow_le_pow_left h10 2; omega)
      omega
    interval_cases p <;> revert hp h2 <;> decide
  · exact key (two_part_ordG2 (by omega)) (ordG2_small (by omega)) h
  · exact key (N := 5) ⟨189, by decide, by norm_num⟩ (by norm_num) h
  · exact key (two_part_ordTrialityD4 he) (ordTrialityD4_small he) h
  · exact key (two_part_ordTwistedF4 (by omega)) (ordTwistedF4_small (by omega)) h
  · exact key (N := 11) ⟨8775, by decide, ordTits_eq⟩ (by rw [ordTits_eq]; norm_num) h

theorem a38Order_not_rankTwoOrder {m : ℕ} (hm : A38Order m) : ¬ RankTwoOrder m := by
  rcases hm with ⟨n, hn, rfl⟩ | ⟨f, hf, hf3, rfl⟩ | rfl | ⟨p, hp, hp3, rfl⟩
  · exact ordA_one_two_pow_not_rankTwoOrder hn
  · exact ordSuzuki_not_rankTwoOrder hf hf3
  · exact j1_not_rankTwoOrder
  · exact ordA_one_prime_not_rankTwoOrder hp hp3

theorem rankTwoOrder_ne_one {m : ℕ} (h : RankTwoOrder m) : m ≠ 1 := by
  have key : ∀ {N : ℕ}, 1 ≤ N → (∃ r, Odd r ∧ m = 2 ^ N * r) → m ≠ 1 := by
    rintro N hN ⟨r, -, rfl⟩ h1
    have h2 : 2 ∣ 2 ^ N * r := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) r
    rw [h1] at h2
    norm_num at h2
  rcases h with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | rfl | ⟨e, he, rfl⟩ |
    rfl | ⟨e, he, rfl⟩ | ⟨k, hk, rfl⟩ | rfl
  · exact key (by omega) (two_part_ordA_two (by omega))
  · exact key (by omega) (two_part_ordTwistedA_three he)
  · exact key (by omega) (two_part_ordTwistedA_four he)
  · exact key (by omega) (two_part_ordBC_two he)
  · norm_num
  · exact key (by omega) (two_part_ordG2 (by omega))
  · norm_num
  · exact key (by omega) (two_part_ordTrialityD4 he)
  · exact key (by omega) (two_part_ordTwistedF4 (by omega))
  · rw [ordTits_eq]
    norm_num

variable {X : Type} [Group X]

theorem isSimpleGroup_of_a38Types
    (h : A38Types X) : IsSimpleGroup X := by
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨p, -, -, hp⟩
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 2 n hn).2
  · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 n hn).2
  · obtain ⟨e⟩ := hJ
    exact @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J1.isSimpleGroup_J1 e
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p 1 hp).2

theorem a38Order_card
    (h : A38Types X) : A38Order (Nat.card X) := by
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨p, hp, hp3, hpsl⟩
  · refine Or.inl ⟨n, ?_, (card_statedClassicalModel_two hn).1 rfl⟩
    obtain ⟨⟨-, hf, -, h22, -⟩, -⟩ := hn
    by_contra hlt
    have hn1 : n = 1 := by omega
    exact h22 (by simp [hn1])
  · obtain ⟨-, a, ha, hf, hcard⟩ := CFSG.GH74.card_of_suzukiModel hn
    exact Or.inr (Or.inl ⟨n, ⟨a, hf⟩, by omega, hcard⟩)
  · obtain ⟨e⟩ := hJ
    refine Or.inr (Or.inr (Or.inl ?_))
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  · refine Or.inr (Or.inr (Or.inr ⟨p, hp, hp3, ?_⟩))
    have h := CFSG.GH74.card_of_lieModel_PSL (by norm_num) (Or.inl ⟨by decide, hpsl⟩)
    simpa using h

theorem isPSL_of_mulEquiv {Y : Type} [Group Y] {n p e : ℕ} (h : IsPSL n p e Y) (φ : Y ≃* X) :
    IsPSL n p e X := by
  obtain ⟨hadm, K, hK1, hK2, hK, ⟨ψ⟩⟩ := h
  exact ⟨hadm, K, hK1, hK2, hK, ⟨φ.symm.trans ψ⟩⟩

end CFSG.Quasithin.H13.VolI
