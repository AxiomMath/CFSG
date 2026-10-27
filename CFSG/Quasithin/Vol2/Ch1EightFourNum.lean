module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.Quasithin.Ch1Four

theorem two_pow_mul_odd_inj {a b r s : ℕ} (hr : Odd r) (hs : Odd s)
    (h : 2 ^ a * r = 2 ^ b * s) : a = b ∧ r = s := by
  have h2 := congrArg (padicValNat 2) h
  have hr2 : ¬ 2 ∣ r := by have := Nat.odd_iff.mp hr; omega
  have hs2 : ¬ 2 ∣ s := by have := Nat.odd_iff.mp hs; omega
  rw [padicValNat.mul (by positivity) hr.pos.ne', padicValNat.mul (by positivity) hs.pos.ne',
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hr2,
    padicValNat.eq_zero_of_not_dvd hs2, add_zero, add_zero] at h2
  subst h2
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

theorem coprime_two_pow_of_odd {n : ℕ} (k : ℕ) (hn : Odd n) : Nat.Coprime (2 ^ k) n :=
  Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hn)

theorem prime_not_dvd_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) : ¬ p ∣ 2 ^ k :=
  fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

theorem prime_dvd_of_dvd_mul_two_pow {p m k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ m * 2 ^ k) : p ∣ m := by
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact h
  · exact absurd h (prime_not_dvd_two_pow hp hp2 k)

theorem mem_of_prime_dvd_prod {p : ℕ} (hp : p.Prime) :
    ∀ L : List ℕ, (∀ q ∈ L, q.Prime) → p ∣ L.prod → p ∈ L
  | [], _, h => by
    simp only [List.prod_nil, Nat.dvd_one] at h
    exact absurd h hp.one_lt.ne'
  | q :: L, hL, h => by
    rw [List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · rw [(Nat.prime_dvd_prime_iff_eq hp (hL q List.mem_cons_self)).mp h1]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_prime_dvd_prod hp L
        (fun x hx => hL x (List.mem_cons_of_mem _ hx)) h1)

theorem sq_sub_one_eq (p : ℕ) : p ^ 2 - 1 = (p + 1) * (p - 1) := by
  rw [← one_pow 2, Nat.sq_sub_sq, one_pow]

theorem cube_sub_one_eq {q : ℕ} (hq : 1 ≤ q) : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
  zify [hq, h3]
  ring

theorem cube_add_one_eq {q : ℕ} (hq : 1 ≤ q) : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
  have h2 : q ≤ q ^ 2 := by nlinarith
  zify [h2]
  ring

theorem four_sub_one_eq {q : ℕ} (hq : 1 ≤ q) : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  zify [h4, h2]
  ring

theorem six_sub_one_eq {q : ℕ} (hq : 1 ≤ q) : q ^ 6 - 1 = (q ^ 3 - 1) * (q ^ 3 + 1) := by
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
  zify [h6, h3]
  ring

theorem pow_add_one_lt_pow {q a b : ℕ} (hq : 2 ≤ q) (ha : 1 ≤ a) (hab : a < b) :
    q ^ a + 1 < q ^ b := by
  have h1 : q ^ (a + 1) ≤ q ^ b := Nat.pow_le_pow_right (by omega) hab
  have h2 : q ^ (a + 1) = q ^ a * q := pow_succ _ _
  have h3 : 2 ≤ q ^ a := by
    calc 2 ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ a := Nat.pow_le_pow_right (by omega) ha
  nlinarith

theorem two_le_pow_of_two_le {q k : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) : 2 ≤ q ^ k :=
  calc 2 ≤ q := hq
    _ = q ^ 1 := (pow_one q).symm
    _ ≤ q ^ k := Nat.pow_le_pow_right (by omega) hk

theorem four_pow_eq (f N : ℕ) : 4 ^ (f * N) = (2 ^ f) ^ (2 * N) := by
  rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  ring_nf

theorem odd_pow_sub_one_of_even {q n : ℕ} (hq : Even q) (hq1 : 1 ≤ q) (hn : 1 ≤ n) :
    Odd (q ^ n - 1) :=
  Nat.Even.sub_odd (Nat.one_le_pow _ _ hq1) ((Nat.even_pow' (by omega)).mpr hq) odd_one

theorem odd_pow_add_one_of_even {q n : ℕ} (hq : Even q) (hn : 1 ≤ n) : Odd (q ^ n + 1) :=
  ((Nat.even_pow' (by omega)).mpr hq).add_one

theorem three_dvd_sq_sub_one (f : ℕ) : 3 ∣ (2 ^ f) ^ 2 - 1 := by
  have h : 4 - 1 ∣ 4 ^ f - 1 ^ f := Nat.sub_dvd_pow_sub_pow 4 1 f
  rw [one_pow] at h
  rwa [← pow_mul, mul_comm, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]

theorem two_pow_le_of_dvd_sq_sub_one {p k : ℕ} (hp : Odd p) (hp3 : 3 ≤ p)
    (h : 2 ^ k ∣ p ^ 2 - 1) : 2 ^ k ≤ 2 * (p + 1) := by
  obtain ⟨a, rfl⟩ := hp
  have ha : 1 ≤ a := by omega
  have e : (2 * a + 1) ^ 2 - 1 = 4 * (a * (a + 1)) := by
    have : (2 * a + 1) ^ 2 = 4 * (a * (a + 1)) + 1 := by ring
    omega
  rw [e] at h
  rcases Nat.lt_or_ge k 3 with hk | hk
  · have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hj : 2 ^ j ∣ a * (a + 1) := by
      rw [pow_add, show (2 : ℕ) ^ 2 = 4 by norm_num, mul_comm] at h
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 4) h
    rcases Nat.even_or_odd a with he | ho
    · have h1 : 2 ^ j ∣ a := (coprime_two_pow_of_odd j (Even.add_one he)).dvd_of_dvd_mul_right hj
      have h2 : 2 ^ j ≤ a := Nat.le_of_dvd (by omega) h1
      rw [pow_add]
      omega
    · have h1 : 2 ^ j ∣ a + 1 := (coprime_two_pow_of_odd j ho).dvd_of_dvd_mul_left hj
      have h2 : 2 ^ j ≤ a + 1 := Nat.le_of_dvd (by omega) h1
      rw [pow_add]
      omega

theorem prime_pow_dvd_of_dvd_sq_sub_one {r p j : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hp : 1 ≤ p)
    (h : r ^ j ∣ p ^ 2 - 1) : r ^ j ∣ p - 1 ∨ r ^ j ∣ p + 1 := by
  rw [sq_sub_one_eq] at h
  by_cases h1 : r ∣ p + 1
  · have h2 : ¬ r ∣ p - 1 := by
      intro h2
      have h3 : r ∣ (p + 1) - (p - 1) := Nat.dvd_sub h1 h2
      rw [show (p + 1) - (p - 1) = 2 by omega] at h3
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h3)
    exact Or.inr ((Nat.Coprime.pow_left j
      ((Nat.Prime.coprime_iff_not_dvd hr).mpr h2)).dvd_of_dvd_mul_right h)
  · exact Or.inl ((Nat.Coprime.pow_left j
      ((Nat.Prime.coprime_iff_not_dvd hr).mpr h1)).dvd_of_dvd_mul_left h)

theorem prime_pow_le_of_dvd_sq_sub_one {r p j : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hp : 2 ≤ p)
    (h : r ^ j ∣ p ^ 2 - 1) : r ^ j ≤ p + 1 := by
  rcases prime_pow_dvd_of_dvd_sq_sub_one hr hr2 (by omega) h with h1 | h1
  · exact (Nat.le_of_dvd (by omega) h1).trans (by omega)
  · exact Nat.le_of_dvd (by omega) h1

theorem not_three_dvd_sz (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1) - 1) := by
  have h2 : (2 ^ (2 * a + 1)) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  generalize 2 ^ (2 * a + 1) = q at h2 hq1 ⊢
  intro h3
  have h1 : (((q ^ 2 * (q ^ 2 + 1) * (q - 1) : ℕ) : ZMod 3)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr h3
  have h2' : (q : ZMod 3) = 2 := by
    rw [← ZMod.natCast_mod, h2]
    rfl
  push_cast [Nat.cast_sub hq1] at h1
  rw [h2'] at h1
  exact absurd h1 (by decide)

@[expose] def finOrders : List ℕ := [60, 168, 360, 1080, 2520, 20160, 443520, 1330560, 244823040]

@[expose] def oddParts : List ℕ := [15, 21, 45, 135, 315, 3465, 10395, 239085]

theorem finOrders_spec {c : ℕ} (hc : c ∈ finOrders) :
    (∃ b, ∃ o ∈ oddParts, c = 2 ^ b * o) ∧ c ∣ 244823040 := by
  simp only [finOrders, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨2, 15, by decide, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨3, 21, by decide, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨3, 45, by decide, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨3, 135, by decide, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨3, 315, by decide, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨6, 315, by decide, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨7, 3465, by decide, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨7, 10395, by decide, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨10, 239085, by decide, by norm_num⟩, by norm_num⟩

theorem oddParts_odd {o : ℕ} (ho : o ∈ oddParts) : Odd o := by
  simp only [oddParts, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem not_fin_of_odd {m a o : ℕ} (hm : m = 2 ^ a * o) (ho : Odd o) (hno : o ∉ oddParts) :
    ∀ c ∈ finOrders, ∀ k, m * 2 ^ k ≠ c := by
  intro c hc k h
  obtain ⟨⟨b, o', ho', rfl⟩, -⟩ := finOrders_spec hc
  have e : 2 ^ (a + k) * o = 2 ^ b * o' := by rw [← h, hm]; ring
  rw [(two_pow_mul_odd_inj ho (oddParts_odd ho') e).2] at hno
  exact hno ho'

theorem le_of_mul_two_pow_eq {m k c : ℕ} (h : m * 2 ^ k = c) : m ≤ c :=
  h ▸ Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)

theorem le_of_mem_finOrders {c : ℕ} (hc : c ∈ finOrders) : c ≤ 244823040 :=
  Nat.le_of_dvd (by norm_num) (finOrders_spec hc).2

theorem le_of_fin {m k c : ℕ} (hc : c ∈ finOrders) (h : m * 2 ^ k = c) : m ≤ 244823040 :=
  (le_of_mul_two_pow_eq h).trans (le_of_mem_finOrders hc)

structure C2Shape (m : ℕ) : Prop where
  fin : ∀ c ∈ finOrders, ∀ k, m * 2 ^ k ≠ c
  three : 3 ∣ m
  shape : ∃ f N d B M : ℕ, 1 ≤ f ∧ 1 ≤ N ∧ (d = 1 ∨ d = 3) ∧ m * d = 2 ^ (f * N) * B ∧ Odd B ∧
    B < 4 ^ (f * N) - 1 ∧ (∀ p, p.Prime → p ∣ B → p ≤ M) ∧ 2 * (M + 1) < 2 ^ (f * N)

namespace C2Shape

variable {m : ℕ}

theorem false_of_two (h : C2Shape m) {n : ℕ} (hn : 1 ≤ n) (hm : m = 2 ^ n * (4 ^ n - 1)) :
    False := by
  obtain ⟨f, N, d, B, M, hf, hN, hd, hmd, hB, hBlt, -, -⟩ := h.shape
  have hodd4 : Odd (4 ^ n - 1) := by
    have : Even (4 ^ n) := (Nat.even_pow' (by omega)).mpr (by decide)
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num)) this odd_one
  have hdodd : Odd d := by rcases hd with rfl | rfl <;> decide
  have e : 2 ^ n * ((4 ^ n - 1) * d) = 2 ^ (f * N) * B := by rw [← hmd, hm]; ring
  obtain ⟨h1, h2⟩ := two_pow_mul_odd_inj (hodd4.mul hdodd) hB e
  have hd1 : 1 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  have : 4 ^ n - 1 ≤ (4 ^ n - 1) * d := Nat.le_mul_of_pos_right _ hd1
  rw [h1] at this h2
  omega

theorem false_of_odd (h : C2Shape m) {p A k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hA : Odd A)
    (hpA : p ∣ A) (hm : m * 2 ^ k = A * (p ^ 2 - 1)) : False := by
  obtain ⟨f, N, d, B, M, hf, hN, hd, hmd, hB, -, hM, hlt⟩ := h.shape
  have hdodd : Odd d := by rcases hd with rfl | rfl <;> decide
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have h1 : 2 ^ (f * N) ∣ m :=
    (coprime_two_pow_of_odd (f * N) hdodd).dvd_of_dvd_mul_right ⟨B, hmd⟩
  have h2 : 2 ^ (f * N) ∣ p ^ 2 - 1 := by
    have : 2 ^ (f * N) ∣ A * (p ^ 2 - 1) := hm ▸ h1.mul_right _
    exact (coprime_two_pow_of_odd (f * N) hA).dvd_of_dvd_mul_left this
  have h3 := two_pow_le_of_dvd_sq_sub_one hpodd (by omega) h2
  have hp2 : p ≠ 2 := by omega
  have h4 : p ∣ m := prime_dvd_of_dvd_mul_two_pow hp hp2 (hm ▸ hpA.mul_right _)
  have h5 : p ∣ B := by
    have : p ∣ 2 ^ (f * N) * B := hmd ▸ h4.mul_right _
    rcases (Nat.Prime.dvd_mul hp).mp this with h | h
    · exact absurd h (prime_not_dvd_two_pow hp hp2 _)
    · exact h
  have h6 := hM p hp h5
  omega

end C2Shape

theorem two_pow_facts {f f₀ : ℕ} (hf : f₀ ≤ f) (hf1 : 1 ≤ f) :
    Even (2 ^ f) ∧ 2 ^ f₀ ≤ 2 ^ f :=
  ⟨(Nat.even_pow' (by omega)).mpr even_two, Nat.pow_le_pow_right (by norm_num) hf⟩

end CFSG.Quasithin.Ch1Four
