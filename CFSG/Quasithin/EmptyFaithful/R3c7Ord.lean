module

public import CFSG.Quasithin.EmptyFaithful.R3c7Ar
public import CFSG.Quasithin.EmptyFaithful.R3c6Fam
public import CFSG.Quasithin.EmptyFaithful.R3c6Spor
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List

public section

namespace CFSG.Quasithin.R3c7

open CFSG.QuasithinUnique.Ch1 (IsFermatOrMersennePrime)

section OddLike

structure OddLike (N : ℕ) : Prop where
  pos : 0 < N
  two_pow : 2 ^ (8 * padicValNat 2 N) ≤ N ^ 3
  prime_power : ∃ p e : ℕ, p.Prime ∧ 5 ≤ p ∧ 1 ≤ e ∧ (p ^ e) ^ 3 ∣ N ∧ N < (p ^ e) ^ 8

theorem OddLike.false_of_big2 {N a b : ℕ} (ho : OddLike N) (ha : padicValNat 2 N = a)
    (hb : N < 2 ^ b) (h1 : 3 * b ≤ 8 * a) : False := by
  have h := ho.two_pow
  rw [ha] at h
  have h3 : N ^ 3 < 2 ^ (8 * a) :=
    calc N ^ 3 < (2 ^ b) ^ 3 := Nat.pow_lt_pow_left hb (by norm_num)
      _ = 2 ^ (3 * b) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ (8 * a) := Nat.pow_le_pow_right (by norm_num) h1
  exact absurd (h.trans_lt h3) (lt_irrefl _)

theorem OddLike.false_of_cubeFree {N : ℕ} (ho : OddLike N)
    (h : ∀ r : ℕ, r.Prime → 5 ≤ r → ¬ r ^ 3 ∣ N) : False := by
  obtain ⟨p, e, hp, hp5, he, hd, -⟩ := ho.prime_power
  exact h p hp hp5 ((pow_dvd_pow_of_dvd (dvd_pow_self p (by omega)) 3).trans hd)

theorem OddLike.false_of_bound {N p0 : ℕ} (ho : OddLike N) (S : Finset ℕ)
    (hS : Nat.primeFactors N = S) (hS' : ∀ r ∈ S, 5 ≤ r → r ≠ p0 → ¬ r ^ 3 ∣ N)
    (hp0 : ¬ (p0 ^ 2) ^ 3 ∣ N) (hbig : p0 ^ 8 ≤ N) : False := by
  have hN0 : N ≠ 0 := ho.pos.ne'
  obtain ⟨p, e, hp, hp5, he, hd, hlt⟩ := ho.prime_power
  have hpd : p ^ 3 ∣ N := (pow_dvd_pow_of_dvd (dvd_pow_self p (by omega)) 3).trans hd
  have hpS : p ∈ S := by
    rw [← hS]
    exact Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans hpd, hN0⟩
  by_cases hpp : p = p0
  · subst hpp
    have he1 : e = 1 := by
      by_contra hne
      have h2 : 2 ≤ e := by omega
      exact hp0 ((pow_dvd_pow_of_dvd (pow_dvd_pow p h2) 3).trans hd)
    subst he1
    rw [pow_one] at hlt
    omega
  · exact hS' p hpS hp5 hpp hpd

theorem OddLike.false_of_prod {N c m : ℕ} (ho : OddLike N) (hc0 : 0 < c) (hc : c ≤ 2)
    (hm : ∀ p e : ℕ, p.Prime → p ≠ 2 → 1 ≤ e → ¬ (p ^ e) ^ 3 ∣ m)
    (h : N * c = m * (m ^ 2 - 1)) : False := by
  have hNpos := ho.pos
  obtain ⟨p, e, hp, hp5, he, hd, hlt⟩ := ho.prime_power
  have hp2 : p ≠ 2 := by omega
  have hq5 : 5 ≤ p ^ e := hp5.trans (Nat.le_self_pow (by omega) p)
  have hdvd : (p ^ e) ^ 3 ∣ m * (m ^ 2 - 1) := by
    rw [← h]; exact hd.trans (dvd_mul_right N c)
  have hNc : 0 < m * (m ^ 2 - 1) := by rw [← h]; exact Nat.mul_pos hNpos hc0
  have hm2 : 2 ≤ m := by
    by_contra hlt2
    have hlt2' : m < 2 := not_le.mp hlt2
    have : m = 0 ∨ m = 1 := by omega
    rcases this with rfl | rfl <;> simp at hNc
  have hcase : (p ^ e) ^ 3 ∣ m - 1 ∨ (p ^ e) ^ 3 ∣ m + 1 := by
    by_cases hpm : p ∣ m
    · exfalso
      have hpn : ¬ p ∣ m ^ 2 - 1 := by
        intro hpd
        have h1 : p ∣ m ^ 2 := dvd_pow hpm (by norm_num)
        have h2 : m ^ 2 - 1 + 1 = m ^ 2 := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
        have : p ∣ 1 := (Nat.dvd_add_right hpd).1 (h2 ▸ h1)
        exact hp.one_lt.ne' (Nat.dvd_one.1 this)
      have hcop : Nat.Coprime ((p ^ e) ^ 3) (m ^ 2 - 1) :=
        (((Nat.Prime.coprime_iff_not_dvd hp).2 hpn).pow_left e).pow_left 3
      exact hm p e hp hp2 he (hcop.dvd_of_dvd_mul_right hdvd)
    · have hcop : Nat.Coprime ((p ^ e) ^ 3) m :=
        (((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).pow_left e).pow_left 3
      have h1 : (p ^ e) ^ 3 ∣ m ^ 2 - 1 := hcop.dvd_of_dvd_mul_left hdvd
      have hfac : m ^ 2 - 1 = (m + 1) * (m - 1) := by
        have := Nat.sq_sub_sq m 1
        simpa using this
      rw [hfac] at h1
      by_cases hpm1 : p ∣ m - 1
      · have hpm1' : ¬ p ∣ m + 1 := by
          intro hpd
          have h3 : p ∣ (m + 1) - (m - 1) := Nat.dvd_sub hpd hpm1
          have h2 : (m + 1) - (m - 1) = 2 := by omega
          rw [h2] at h3
          have := Nat.le_of_dvd (by norm_num) h3
          omega
        have hcop2 : Nat.Coprime ((p ^ e) ^ 3) (m + 1) :=
          (((Nat.Prime.coprime_iff_not_dvd hp).2 hpm1').pow_left e).pow_left 3
        exact Or.inl (hcop2.dvd_of_dvd_mul_left h1)
      · have hcop2 : Nat.Coprime ((p ^ e) ^ 3) (m - 1) :=
          (((Nat.Prime.coprime_iff_not_dvd hp).2 hpm1).pow_left e).pow_left 3
        exact Or.inr (hcop2.dvd_of_dvd_mul_right h1)
  have hle : (p ^ e) ^ 3 ≤ m + 1 := by
    rcases hcase with hd1 | hd1
    · have := Nat.le_of_dvd (by omega) hd1
      omega
    · exact Nat.le_of_dvd (by omega) hd1
  have hmge : (p ^ e) ^ 3 - 1 ≤ m := by omega
  have h1 := CFSG.Quasithin.R3c6.two_mul_pow_eight_lt hq5
  have h2 : ((p ^ e) ^ 3 - 1) * (((p ^ e) ^ 3 - 1) ^ 2 - 1) ≤ m * (m ^ 2 - 1) :=
    Nat.mul_le_mul hmge (Nat.sub_le_sub_right (Nat.pow_le_pow_left hmge 2) 1)
  have h3 : N * c ≤ N * 2 := Nat.mul_le_mul_left N hc
  have h4 : N * 2 < 2 * (p ^ e) ^ 8 := by omega
  omega

end OddLike


section Class

inductive OrdClass : ℕ → Prop
  | big2 {N a b : ℕ} (ha : padicValNat 2 N = a) (hb : N < 2 ^ b) (h1 : 3 * b ≤ 8 * a)
      (h2 : b + 2 ≤ 3 * a) : OrdClass N
  | l3two {N : ℕ} (h : N = 168) : OrdClass N
  | l2two {f N : ℕ} (hf : 2 ≤ f) (h : N = 2 ^ f * ((2 ^ f) ^ 2 - 1)) : OrdClass N
  | l2fm {p N : ℕ} (hp : IsFermatOrMersennePrime p) (h : N * 2 = p * (p ^ 2 - 1)) : OrdClass N
  | small {N : ℕ} (h : N = 360 ∨ N = 2520 ∨ N = 5616) : OrdClass N
  | spor {N : ℕ} (h : IsSporOrder N) : OrdClass N

theorem OrdClass.false_of_oddLike {N : ℕ} (hc : OrdClass N) (ho : OddLike N) : False := by
  cases hc with
  | big2 ha hb h1 h2 => exact ho.false_of_big2 ha hb h1
  | l3two h =>
    subst h
    exact ho.false_of_cubeFree (CFSG.Quasithin.R3c6.cubeFree_of_bounded (B := 5) (by norm_num)
      (by norm_num) (by decide))
  | l2two hf h =>
    refine ho.false_of_prod (c := 1) (m := 2 ^ (_ : ℕ)) one_pos (by norm_num) ?_ (by rw [mul_one, h])
    intro p e hp hp2 he hd
    have h1 : p ∣ 2 ^ (_ : ℕ) :=
      (dvd_pow_self p (by omega)).trans ((dvd_pow_self (p ^ e) (by norm_num)).trans hd)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1))
  | l2fm hp h =>
    refine ho.false_of_prod (c := 2) (m := _) (by norm_num) le_rfl ?_ h
    intro p e hp0 hp2 he hd
    rcases (Nat.dvd_prime hp.1).1 hd with h1 | h1
    · have h2 : 1 < (p ^ e) ^ 3 :=
        Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow (by omega) hp0.one_lt)
      omega
    · rw [← pow_mul] at h1
      exact Nat.Prime.not_prime_pow (by omega : 2 ≤ e * 3) (h1 ▸ hp.1)
  | small h =>
    rcases h with rfl | rfl | rfl
    · exact ho.false_of_cubeFree (CFSG.Quasithin.R3c6.cubeFree_of_bounded (B := 7) (by norm_num)
        (by norm_num) (by decide))
    · exact ho.false_of_cubeFree (CFSG.Quasithin.R3c6.cubeFree_of_bounded (B := 13) (by norm_num)
        (by norm_num) (by decide))
    · exact ho.false_of_cubeFree (CFSG.Quasithin.R3c6.cubeFree_of_bounded (B := 17) (by norm_num)
        (by norm_num) (by decide))
  | spor h =>
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ho.false_of_cubeFree (CFSG.Quasithin.R3c6.cubeFree_of_primeFactors (by norm_num)
        {2, 3, 5, 11} (by norm_num [Nat.primeFactors]) (by decide))
    · exact ho.false_of_cubeFree (CFSG.Quasithin.R3c6.cubeFree_of_primeFactors (by norm_num)
        {2, 3, 5, 11} (by norm_num [Nat.primeFactors]) (by decide))
    · exact ho.false_of_cubeFree (CFSG.Quasithin.R3c6.cubeFree_of_primeFactors (by norm_num)
        {2, 3, 5, 7, 11} (by norm_num [Nat.primeFactors]) (by decide))
    · exact ho.false_of_cubeFree (CFSG.Quasithin.R3c6.cubeFree_of_primeFactors (by norm_num)
        {2, 3, 5, 7, 11, 23} (by norm_num [Nat.primeFactors]) (by decide))
    · exact ho.false_of_cubeFree (CFSG.Quasithin.R3c6.cubeFree_of_primeFactors (by norm_num)
        {2, 3, 5, 7, 11, 23} (by norm_num [Nat.primeFactors]) (by decide))
    · exact ho.false_of_cubeFree (CFSG.Quasithin.R3c6.cubeFree_of_primeFactors (by norm_num)
        {2, 3, 5, 7} (by norm_num [Nat.primeFactors]) (by decide))
    · exact ho.false_of_bound (p0 := 11) {2, 3, 5, 7, 11, 23, 29, 31, 37, 43}
        (by norm_num [Nat.primeFactors]) (by decide) (by norm_num) (by norm_num)
    · exact ho.false_of_bound (p0 := 5) {2, 3, 5, 7, 11} (by norm_num [Nat.primeFactors])
        (by decide) (by norm_num) (by norm_num)
    · exact ho.false_of_bound (p0 := 7) {2, 3, 5, 7, 17} (by norm_num [Nat.primeFactors])
        (by decide) (by norm_num) (by norm_num)
    · exact ho.false_of_bound (p0 := 5) {2, 3, 5, 7, 13, 29} (by norm_num [Nat.primeFactors])
        (by decide) (by norm_num) (by norm_num)

end Class


section Dispatch

theorem padicValNat_l2two {f N : ℕ} (hf : 1 ≤ f) (h : N = 2 ^ f * ((2 ^ f) ^ 2 - 1)) :
    padicValNat 2 N = f :=
  CFSG.Quasithin.R3c6.padicValNat_eq_of_mul_odd (g := 1) odd_one
    (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega : 0 < f) (by norm_num : 0 < 2)) (a := f)
    (by rw [mul_one, h])

theorem OrdClass.false_of_l2sq {N p : ℕ} (hc : OrdClass N) (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : N * 2 = p ^ 2 * (p ^ 4 - 1)) : False := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hlt := two_pow_three_lt_of_l2sq hodd hp5 h
  have hge := le_of_l2sq hp5 h
  cases hc with
  | @big2 _ a b ha hb h1 h2 =>
    rw [ha] at hlt
    have : 2 ^ b ≤ 2 ^ (3 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  | l3two h => omega
  | @l2two f _ hf h' =>
    rw [padicValNat_l2two (by omega) h'] at hlt
    have h8 : N < 2 ^ (3 * f) := by
      have h1 : (2 ^ f) ^ 2 - 1 < (2 ^ f) ^ 2 := Nat.sub_lt (by positivity) one_pos
      calc N = 2 ^ f * ((2 ^ f) ^ 2 - 1) := h'
        _ < 2 ^ f * (2 ^ f) ^ 2 := Nat.mul_lt_mul_of_pos_left h1 (by positivity)
        _ = 2 ^ (3 * f) := by ring
    omega
  | @l2fm p' _ hp' h' =>
    have e : p' * (p' ^ 2 - 1) = p ^ 2 * ((p ^ 2) ^ 2 - 1) := by
      rw [← h', h, ← pow_mul]
    have := eq_of_mul_sq_sub_one_eq (hp'.1.one_lt.le) (Nat.one_le_pow _ _ (by omega)) e
    exact Nat.Prime.not_prime_pow (by norm_num : 2 ≤ 2) (this ▸ hp'.1)
  | small h' => rcases h' with rfl | rfl | rfl <;> omega
  | spor h' => exact (l2_spor_false h').2 p hp (by omega) h

end Dispatch


section Dispatch2

theorem OrdClass.l2p {N p : ℕ} (hc : OrdClass N) (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7)
    (h : N * 2 = p * (p ^ 2 - 1)) : p = 7 ∨ IsFermatOrMersennePrime p := by
  have hp7 : 7 ≤ p := by
    have := hp.two_le
    rcases hp8 with h8 | h8
    · by_contra hlt
      omega
    · omega
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  cases hc with
  | @big2 _ a b ha hb h1 h2 =>
    have h3 := two_pow_three_le_of_l2p hodd hp7 h
    rw [ha] at h3
    have h4 : 2 ^ (b + 2) ≤ 2 ^ (3 * a) := Nat.pow_le_pow_right (by norm_num) h2
    have h5 : 4 * N < 2 ^ (b + 2) := by rw [pow_add]; omega
    omega
  | l3two h' =>
    left
    have e : p * (p ^ 2 - 1) = 7 * (7 ^ 2 - 1) := by rw [← h, h']; norm_num
    exact eq_of_mul_sq_sub_one_eq (by omega) (by norm_num) e
  | @l2two f _ hf h' => exact (false_of_l2two_l2p hf h' hp hp8 h).elim
  | @l2fm p' _ hp' h' =>
    right
    have := eq_of_l2_orders (by omega) hp'.1.one_lt.le h h'
    exact this ▸ hp'
  | small h' => exact (false_of_l2p_small h' hp h).elim
  | spor h' => exact ((l2_spor_false h').1 p hp (by omega) h).elim

end Dispatch2


section OddLikeOrders

theorem su3_num_lt {p : ℕ} (hp : 2 ≤ p) : p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) < p ^ 8 := by
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h5 : p ^ 5 < p ^ 6 := Nat.pow_lt_pow_right hp (by norm_num)
  have h5' : (p : ℤ) ^ 5 < (p : ℤ) ^ 6 := by exact_mod_cast h5
  have h3 : (0 : ℤ) ≤ (p : ℤ) ^ 3 := by positivity
  zify [h1]
  nlinarith [h5', h3]

theorem sl3_num_lt {p : ℕ} (hp : 2 ≤ p) : p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) < p ^ 8 := by
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h5 : p ^ 5 < p ^ 6 := Nat.pow_lt_pow_right hp (by norm_num)
  have h5' : (p : ℤ) ^ 5 < (p : ℤ) ^ 6 := by exact_mod_cast h5
  have h3 : (0 : ℤ) ≤ (p : ℤ) ^ 3 := by positivity
  have h6 : (p : ℤ) ^ 3 < (p : ℤ) ^ 5 := by
    have : p ^ 3 < p ^ 5 := Nat.pow_lt_pow_right hp (by norm_num)
    exact_mod_cast this
  zify [h1, h2]
  nlinarith [h5', h3, h6]

theorem oddLike_of_su3 {p N g : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hg : g = Nat.gcd 3 (p + 1))
    (h : N * g = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1))) : OddLike N := by
  have hg3 : g ∣ 3 := hg ▸ Nat.gcd_dvd_left 3 _
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hg0 : 0 < g := Nat.pos_of_ne_zero (by rintro rfl; simp at hg3)
  have hpos : 0 < N * g := by
    rw [h]
    have h1 : 1 ≤ p ^ 2 - 1 := by
      have : 4 ≤ p ^ 2 := by nlinarith
      omega
    positivity
  refine ⟨Nat.pos_of_mul_pos_right hpos, ?_, p, 1, hp, hp5, le_rfl, ?_, ?_⟩
  · exact CFSG.Quasithin.R3c6.two_pow_le_of_su3 hodd hp5 (g := g) (by rw [h, mul_assoc]) hg3
  · rw [pow_one]
    have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
    have h2 : Nat.Coprime (p ^ 3) g :=
      Nat.Coprime.coprime_dvd_right hg3 (hcop.pow_left 3)
    exact h2.dvd_of_dvd_mul_right (by rw [h]; exact dvd_mul_right _ _)
  · rw [pow_one]
    have h3 := su3_num_lt (by omega : 2 ≤ p)
    have h4 : N ≤ N * g := Nat.le_mul_of_pos_right N hg0
    omega

theorem oddLike_of_sl3 {p N g : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hg : g = Nat.gcd 3 (p - 1))
    (h : N * g = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1))) : OddLike N := by
  have hg3 : g ∣ 3 := hg ▸ Nat.gcd_dvd_left 3 _
  have hgq : g ∣ p - 1 := hg ▸ Nat.gcd_dvd_right 3 _
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hg0 : 0 < g := Nat.pos_of_ne_zero (by rintro rfl; simp at hg3)
  have hpos : 0 < N * g := by
    rw [h]
    have h1 : 1 ≤ p ^ 2 - 1 := by
      have : 4 ≤ p ^ 2 := by nlinarith
      omega
    have h2 : 1 ≤ p ^ 3 - 1 := by
      have : 8 ≤ p ^ 3 := by nlinarith [Nat.pow_le_pow_left hp5 3]
      omega
    positivity
  refine ⟨Nat.pos_of_mul_pos_right hpos, ?_, p, 1, hp, hp5, le_rfl, ?_, ?_⟩
  · refine CFSG.RankThree.PartTwo.KFacts.OddChar.two_pow_le_of_mul_eq_slOrd hodd (by omega)
      (n := 3) (g := g) le_rfl ?_ hgq
    rw [h]
    have hI : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
    rw [hI, Finset.prod_pair (by norm_num)]
  · rw [pow_one]
    have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
    have h2 : Nat.Coprime (p ^ 3) g :=
      Nat.Coprime.coprime_dvd_right hg3 (hcop.pow_left 3)
    exact h2.dvd_of_dvd_mul_right (by rw [h]; exact dvd_mul_right _ _)
  · rw [pow_one]
    have h3 := sl3_num_lt (by omega : 2 ≤ p)
    have h4 : N ≤ N * g := Nat.le_mul_of_pos_right N hg0
    omega

end OddLikeOrders

end CFSG.Quasithin.R3c7
