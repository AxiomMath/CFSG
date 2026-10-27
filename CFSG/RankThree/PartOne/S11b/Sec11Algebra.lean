module

public import Mathlib.GroupTheory.Exponent
public import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic.Group
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.RankThree.PartOne.Sec11Algebra

variable {G : Type*} [Group G]

theorem pow_mul_eq_of_comm_central {a c d : G} (hd : c * a = a * c * d)
    (hdz : ∀ g : G, g * d = d * g) (k : ℕ) : c ^ k * a = a * c ^ k * d ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : d * c ^ k = c ^ k * d := (hdz (c ^ k)).symm
    have h2 : d ^ k * d = d * d ^ k := (hdz (d ^ k))
    calc c ^ (k + 1) * a = c * (c ^ k * a) := by rw [pow_succ', mul_assoc]
      _ = c * (a * c ^ k * d ^ k) := by rw [ih]
      _ = (c * a) * c ^ k * d ^ k := by group
      _ = (a * c * d) * c ^ k * d ^ k := by rw [hd]
      _ = a * c * (d * c ^ k) * d ^ k := by group
      _ = a * c * (c ^ k * d) * d ^ k := by rw [h1]
      _ = a * (c * c ^ k) * (d * d ^ k) := by
        rw [← h2]; group
      _ = a * c ^ (k + 1) * d ^ (k + 1) := by rw [pow_succ' c k, pow_succ' d k]

theorem central_swap {z : G} (hz : ∀ g : G, g * z = z * g) (x y : G) :
    x * z * y = x * y * z := by
  rw [mul_assoc, ← hz y, ← mul_assoc]

theorem central_pow {z : G} (hz : ∀ g : G, g * z = z * g) (k : ℕ) (g : G) :
    g * z ^ k = z ^ k * g :=
  (Commute.pow_right (show Commute g z from hz g) k).eq

theorem mul_pow_eq_of_comm_central {b c e : G} (he : c * b = b * c * e)
    (hez : ∀ g : G, g * e = e * g) (k : ℕ) : c * b ^ k = b ^ k * c * e ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := central_pow hez k
    calc c * b ^ (k + 1) = (c * b ^ k) * b := by rw [pow_succ, ← mul_assoc]
      _ = b ^ k * c * e ^ k * b := by rw [ih]
      _ = b ^ k * c * b * e ^ k := by rw [central_swap hk]
      _ = b ^ k * (c * b) * e ^ k := by rw [mul_assoc (b ^ k) c b]
      _ = b ^ k * (b * c * e) * e ^ k := by rw [he]
      _ = b ^ k * b * c * (e * e ^ k) := by
        simp only [mul_assoc]
      _ = b ^ (k + 1) * c * e ^ (k + 1) := by rw [pow_succ b k, pow_succ' e k]

theorem pow_mul_eq_of_comm_central' {b c e : G} (he : c * b = b * c * e)
    (hez : ∀ g : G, g * e = e * g) (k : ℕ) : c ^ k * b = b * c ^ k * e ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := central_pow hez k
    calc c ^ (k + 1) * b = c * (c ^ k * b) := by rw [pow_succ', mul_assoc]
      _ = c * (b * c ^ k * e ^ k) := by rw [ih]
      _ = (c * b) * c ^ k * e ^ k := by simp only [mul_assoc]
      _ = (b * c * e) * c ^ k * e ^ k := by rw [he]
      _ = b * c * (e * c ^ k) * e ^ k := by simp only [mul_assoc]
      _ = b * c * (c ^ k * e) * e ^ k := by rw [← hez (c ^ k)]
      _ = b * (c * c ^ k) * (e * e ^ k) := by simp only [mul_assoc]
      _ = b * c ^ (k + 1) * e ^ (k + 1) := by rw [pow_succ' c k, pow_succ' e k]

theorem pow_mul_eq_of_class_three {a b c e : G} (hc : b * a = a * b * c) (he : c * b = b * c * e)
    (hez : ∀ g : G, g * e = e * g) (k : ℕ) :
    b ^ k * a = a * b ^ k * c ^ k * e ^ k.choose 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hcb := mul_pow_eq_of_comm_central he hez k
    have hk := central_pow hez k
    have hk2 := central_pow hez (k.choose 2)
    calc b ^ (k + 1) * a = b * (b ^ k * a) := by rw [pow_succ', mul_assoc]
      _ = b * (a * b ^ k * c ^ k * e ^ k.choose 2) := by rw [ih]
      _ = (b * a) * b ^ k * c ^ k * e ^ k.choose 2 := by simp only [mul_assoc]
      _ = (a * b * c) * b ^ k * c ^ k * e ^ k.choose 2 := by rw [hc]
      _ = a * b * (c * b ^ k) * c ^ k * e ^ k.choose 2 := by simp only [mul_assoc]
      _ = a * b * (b ^ k * c * e ^ k) * c ^ k * e ^ k.choose 2 := by rw [hcb]
      _ = a * (b * b ^ k) * c * (e ^ k * c ^ k) * e ^ k.choose 2 := by simp only [mul_assoc]
      _ = a * (b * b ^ k) * c * (c ^ k * e ^ k) * e ^ k.choose 2 := by rw [← hk (c ^ k)]
      _ = a * b ^ (k + 1) * c ^ (k + 1) * e ^ (k + 1).choose 2 := by
        have h1 : (k + 1).choose 2 = k + k.choose 2 := by
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
        rw [h1, pow_succ' b k, pow_succ' c k, pow_add e k (k.choose 2)]
        simp only [mul_assoc]

theorem pow_mul_mul_eq {a b c d e : G} (hd : c * a = a * c * d) (he : c * b = b * c * e)
    (hdz : ∀ g : G, g * d = d * g) (hez : ∀ g : G, g * e = e * g) (k : ℕ) :
    c ^ k * (a * b) = a * b * c ^ k * (d ^ k * e ^ k) := by
  have h1 := pow_mul_eq_of_comm_central hd hdz k
  have h2 := pow_mul_eq_of_comm_central' he hez k
  have hdk := central_pow hdz k
  have hek := central_pow hez k
  calc c ^ k * (a * b) = (c ^ k * a) * b := by rw [mul_assoc]
    _ = (a * c ^ k * d ^ k) * b := by rw [h1]
    _ = a * c ^ k * b * d ^ k := by rw [central_swap hdk]
    _ = a * (c ^ k * b) * d ^ k := by simp only [mul_assoc]
    _ = a * (b * c ^ k * e ^ k) * d ^ k := by rw [h2]
    _ = a * b * c ^ k * (e ^ k * d ^ k) := by simp only [mul_assoc]
    _ = a * b * c ^ k * (d ^ k * e ^ k) := by rw [central_pow hdz k (e ^ k)]

theorem pow_mul_mul_eq' {a b c e : G} (hc : b * a = a * b * c) (he : c * b = b * c * e)
    (hez : ∀ g : G, g * e = e * g) (n : ℕ) :
    b ^ n * a * b = a * b ^ (n + 1) * c ^ n * e ^ (n + n.choose 2) := by
  have h1 := pow_mul_eq_of_class_three hc he hez n
  have h2 := pow_mul_eq_of_comm_central' he hez n
  have hen := central_pow hez (n.choose 2)
  calc b ^ n * a * b = (a * b ^ n * c ^ n * e ^ n.choose 2) * b := by rw [h1]
    _ = a * b ^ n * c ^ n * b * e ^ n.choose 2 := by rw [central_swap hen]
    _ = a * b ^ n * (c ^ n * b) * e ^ n.choose 2 := by simp only [mul_assoc]
    _ = a * b ^ n * (b * c ^ n * e ^ n) * e ^ n.choose 2 := by rw [h2]
    _ = a * (b ^ n * b) * c ^ n * (e ^ n * e ^ n.choose 2) := by simp only [mul_assoc]
    _ = a * b ^ (n + 1) * c ^ n * e ^ (n + n.choose 2) := by
        rw [pow_succ b n, pow_add e n (n.choose 2)]

theorem add_two_mul_choose_two (n : ℕ) : n + 2 * n.choose 2 = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith [ih]

theorem central_mix {d e : G} (hdz : ∀ g : G, g * d = d * g) (i j k l m : ℕ) :
    e ^ i * (d ^ j * e ^ k) * (d ^ l * e ^ m) = d ^ (j + l) * e ^ (i + k + m) := by
  have hed : e ^ i * d ^ j = d ^ j * e ^ i := central_pow hdz j (e ^ i)
  have hed2 : e ^ (i + k) * d ^ l = d ^ l * e ^ (i + k) := central_pow hdz l (e ^ (i + k))
  calc e ^ i * (d ^ j * e ^ k) * (d ^ l * e ^ m)
      = (e ^ i * d ^ j) * e ^ k * (d ^ l * e ^ m) := by simp only [mul_assoc]
    _ = d ^ j * e ^ i * e ^ k * (d ^ l * e ^ m) := by rw [hed]
    _ = d ^ j * (e ^ (i + k) * d ^ l) * e ^ m := by rw [pow_add]; simp only [mul_assoc]
    _ = d ^ j * (d ^ l * e ^ (i + k)) * e ^ m := by rw [hed2]
    _ = d ^ (j + l) * e ^ (i + k + m) := by
      rw [pow_add d j l, pow_add e (i + k) m]
      simp only [mul_assoc]

theorem pow_mul_of_class_three {a b c d e : G} (hc : b * a = a * b * c)
    (hd : c * a = a * c * d) (he : c * b = b * c * e) (hdz : ∀ g : G, g * d = d * g)
    (hez : ∀ g : G, g * e = e * g) (n : ℕ) :
    (a * b) ^ n = a ^ n * b ^ n * c ^ n.choose 2 *
      (d ^ n.choose 3 * e ^ (∑ k ∈ Finset.range n, k ^ 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hZ : ∀ g : G, g * (d ^ n.choose 3 * e ^ (∑ k ∈ Finset.range n, k ^ 2)) =
        (d ^ n.choose 3 * e ^ (∑ k ∈ Finset.range n, k ^ 2)) * g := by
      intro g
      rw [← mul_assoc, central_pow hdz _ g, mul_assoc, central_pow hez _ g, mul_assoc]
    have h1 := pow_mul_mul_eq hd he hdz hez (n.choose 2)
    have h2 := pow_mul_mul_eq' hc he hez n
    have hsq : ∑ k ∈ Finset.range (n + 1), k ^ 2 = ∑ k ∈ Finset.range n, k ^ 2 + n ^ 2 :=
      Finset.sum_range_succ _ _
    have hc3 : (n + 1).choose 3 = n.choose 2 + n.choose 3 := by
      rw [Nat.choose_succ_succ]
    have hc2 : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    have hcen : ∀ (i : ℕ), ∀ x y : G, x * e ^ i * y = x * y * e ^ i :=
      fun i => central_swap (central_pow hez i)
    calc (a * b) ^ (n + 1) = (a * b) ^ n * (a * b) := by rw [pow_succ]
      _ = a ^ n * b ^ n * c ^ n.choose 2 *
          (d ^ n.choose 3 * e ^ (∑ k ∈ Finset.range n, k ^ 2)) * (a * b) := by rw [ih]
      _ = a ^ n * b ^ n * c ^ n.choose 2 * (a * b) *
          (d ^ n.choose 3 * e ^ (∑ k ∈ Finset.range n, k ^ 2)) := by rw [central_swap hZ]
      _ = a ^ n * b ^ n * (c ^ n.choose 2 * (a * b)) *
          (d ^ n.choose 3 * e ^ (∑ k ∈ Finset.range n, k ^ 2)) := by simp only [mul_assoc]
      _ = a ^ n * b ^ n * (a * b * c ^ n.choose 2 * (d ^ n.choose 2 * e ^ n.choose 2)) *
          (d ^ n.choose 3 * e ^ (∑ k ∈ Finset.range n, k ^ 2)) := by rw [h1]
      _ = a ^ n * (b ^ n * a * b) * c ^ n.choose 2 * (d ^ n.choose 2 * e ^ n.choose 2) *
          (d ^ n.choose 3 * e ^ (∑ k ∈ Finset.range n, k ^ 2)) := by simp only [mul_assoc]
      _ = a ^ n * (a * b ^ (n + 1) * c ^ n * e ^ (n + n.choose 2)) * c ^ n.choose 2 *
          (d ^ n.choose 2 * e ^ n.choose 2) *
          (d ^ n.choose 3 * e ^ (∑ k ∈ Finset.range n, k ^ 2)) := by rw [h2]
      _ = a ^ n * (a * b ^ (n + 1) * c ^ n * c ^ n.choose 2 * e ^ (n + n.choose 2)) *
          (d ^ n.choose 2 * e ^ n.choose 2) *
          (d ^ n.choose 3 * e ^ (∑ k ∈ Finset.range n, k ^ 2)) := by
        rw [mul_assoc (a ^ n) _ (c ^ n.choose 2), hcen (n + n.choose 2) (a * b ^ (n + 1) * c ^ n)
          (c ^ n.choose 2)]
      _ = a ^ (n + 1) * b ^ (n + 1) * c ^ (n + n.choose 2) *
          (e ^ (n + n.choose 2) * (d ^ n.choose 2 * e ^ n.choose 2) *
          (d ^ n.choose 3 * e ^ (∑ k ∈ Finset.range n, k ^ 2))) := by
        rw [pow_succ a n, pow_add c n (n.choose 2)]
        simp only [mul_assoc]
      _ = a ^ (n + 1) * b ^ (n + 1) * c ^ (n + 1).choose 2 *
          (d ^ (n + 1).choose 3 * e ^ (∑ k ∈ Finset.range (n + 1), k ^ 2)) := by
        have hex : n + n.choose 2 + n.choose 2 + ∑ k ∈ Finset.range n, k ^ 2 =
            ∑ k ∈ Finset.range n, k ^ 2 + n ^ 2 := by
          have := add_two_mul_choose_two n
          omega
        rw [central_mix hdz, hc3, hc2, hsq, hex]

theorem six_mul_sum_sq (m : ℕ) :
    6 * ∑ k ∈ Finset.range (m + 1), k ^ 2 = m * (m + 1) * (2 * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

theorem prime_dvd_binomials {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    p ∣ p.choose 2 ∧ p ∣ p.choose 3 ∧ p ∣ ∑ k ∈ Finset.range p, k ^ 2 := by
  refine ⟨hp.dvd_choose_self (by norm_num) (by omega), hp.dvd_choose_self (by norm_num)
    (by omega), ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  have h6 := six_mul_sum_sq m
  have hdvd : (m + 1) ∣ 6 * ∑ k ∈ Finset.range (m + 1), k ^ 2 := by
    rw [h6]
    exact ⟨m * (2 * m + 1), by ring⟩
  have hcop : Nat.Coprime (m + 1) 6 := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have h6' : (m + 1) ≤ 6 := Nat.le_of_dvd (by norm_num) h
    have hm : m ≤ 5 := by omega
    interval_cases m <;> first | omega | (norm_num at h; done) | exact absurd hp (by decide)
  exact hcop.dvd_of_dvd_mul_left hdvd

theorem exists_pow_eq_of_relations {T : Type*} [Group T] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (x y : T) (Q W : Subgroup T) (hWQ : W ≤ Q) (hQc : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q)
    (hWz : ∀ w ∈ W, ∀ g : T, g * w = w * g) (hc : y⁻¹ * x⁻¹ * y * x ∈ Q)
    (hQx : ∀ q ∈ Q, q⁻¹ * x⁻¹ * q * x ∈ W) (hQy : ∀ q ∈ Q, q⁻¹ * y⁻¹ * q * y ∈ W)
    (hxy : x ^ p * y ^ p = 1) {z : T} (hz : z ∈ Q) :
    ∃ q ∈ Q, (x * y * z) ^ p = q ^ p := by
  obtain ⟨⟨i2, hi2⟩, ⟨i3, hi3⟩, ⟨iS, hiS⟩⟩ := prime_dvd_binomials hp hp5
  have hcom : ∀ q ∈ Q, ∀ q' ∈ Q, Commute q q' := fun q hq q' hq' => hQc q hq q' hq'
  obtain ⟨c, hcdef⟩ : ∃ c : T, c = y⁻¹ * x⁻¹ * y * x := ⟨_, rfl⟩
  obtain ⟨d, hddef⟩ : ∃ d : T, d = c⁻¹ * x⁻¹ * c * x := ⟨_, rfl⟩
  obtain ⟨e, hedef⟩ : ∃ e : T, e = c⁻¹ * y⁻¹ * c * y := ⟨_, rfl⟩
  have hcQ : c ∈ Q := hcdef ▸ hc
  have hdW : d ∈ W := hddef ▸ hQx c hcQ
  have heW : e ∈ W := hedef ▸ hQy c hcQ
  have hdz : ∀ g : T, g * d = d * g := hWz d hdW
  have hez : ∀ g : T, g * e = e * g := hWz e heW
  have hrel1 : y * x = x * y * c := by rw [hcdef]; group
  have hrel2 : c * x = x * c * d := by rw [hddef]; group
  have hrel3 : c * y = y * c * e := by rw [hedef]; group
  have hxyp := pow_mul_of_class_three hrel1 hrel2 hrel3 hdz hez p
  have hdQ : d ∈ Q := hWQ hdW
  have heQ : e ∈ Q := hWQ heW
  have hq₁Q : c ^ i2 * (d ^ i3 * e ^ iS) ∈ Q :=
    Q.mul_mem (Q.pow_mem hcQ _) (Q.mul_mem (Q.pow_mem hdQ _) (Q.pow_mem heQ _))
  have hcorr : c ^ p.choose 2 * (d ^ p.choose 3 * e ^ (∑ k ∈ Finset.range p, k ^ 2)) =
      (c ^ i2 * (d ^ i3 * e ^ iS)) ^ p := by
    have hde : Commute (d ^ i3) (e ^ iS) :=
      Commute.pow_pow (hcom d hdQ e heQ) i3 iS
    have hcde : Commute (c ^ i2) (d ^ i3 * e ^ iS) :=
      (Commute.pow_pow (hcom c hcQ d hdQ) i2 i3).mul_right
        (Commute.pow_pow (hcom c hcQ e heQ) i2 iS)
    rw [hcde.mul_pow, hde.mul_pow, hi2, hi3, hiS, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm i2 p,
      mul_comm i3 p, mul_comm iS p]
  obtain ⟨wx, hwxdef⟩ : ∃ w : T, w = z⁻¹ * x⁻¹ * z * x := ⟨_, rfl⟩
  obtain ⟨wy, hwydef⟩ : ∃ w : T, w = z⁻¹ * y⁻¹ * z * y := ⟨_, rfl⟩
  have hwx : wx ∈ W := hwxdef ▸ hQx z hz
  have hwy : wy ∈ W := hwydef ▸ hQy z hz
  have hzx : z * x = x * z * wx := by rw [hwxdef]; group
  have hzy : z * y = y * z * wy := by rw [hwydef]; group
  have hzu : z * (x * y) = x * y * z * (wy * wx) := by
    calc z * (x * y) = (z * x) * y := by rw [mul_assoc]
      _ = x * z * wx * y := by rw [hzx]
      _ = x * z * y * wx := by rw [central_swap (hWz wx hwx)]
      _ = x * (z * y) * wx := by simp only [mul_assoc]
      _ = x * (y * z * wy) * wx := by rw [hzy]
      _ = x * y * z * (wy * wx) := by simp only [mul_assoc]
  have htW : wy * wx ∈ W := W.mul_mem hwy hwx
  have htz := hWz (wy * wx) htW
  have hP := pow_mul_of_class_three (a := x * y) (b := z) (c := wy * wx) (d := 1) (e := 1) hzu
    (by rw [mul_one]; exact (htz (x * y)).symm) (by rw [mul_one]; exact (htz z).symm)
    (fun g => by simp) (fun g => by simp) p
  simp only [one_pow, mul_one] at hP
  have htQ : (wy * wx) ^ i2 ∈ Q := Q.pow_mem (hWQ htW) _
  have hu : (x * y) ^ p = (c ^ i2 * (d ^ i3 * e ^ iS)) ^ p := by
    rw [hxyp, mul_assoc (x ^ p * y ^ p) (c ^ p.choose 2), hcorr, hxy, one_mul]
  have ht : (wy * wx) ^ p.choose 2 = ((wy * wx) ^ i2) ^ p := by
    rw [hi2, ← pow_mul, mul_comm]
  have hq : ((c ^ i2 * (d ^ i3 * e ^ iS)) * z * (wy * wx) ^ i2) ^ p =
      (c ^ i2 * (d ^ i3 * e ^ iS)) ^ p * z ^ p * ((wy * wx) ^ i2) ^ p := by
    have h1 : Commute (c ^ i2 * (d ^ i3 * e ^ iS) * z) ((wy * wx) ^ i2) :=
      hcom _ (Q.mul_mem hq₁Q hz) _ htQ
    have h2 : Commute (c ^ i2 * (d ^ i3 * e ^ iS)) z := hcom _ hq₁Q _ hz
    rw [h1.mul_pow, h2.mul_pow]
  exact ⟨(c ^ i2 * (d ^ i3 * e ^ iS)) * z * (wy * wx) ^ i2,
    Q.mul_mem (Q.mul_mem hq₁Q hz) htQ, by rw [hP, hu, ht, hq]⟩

theorem orderOf_dvd_exponent_of_relations {T : Type*} [Group T] [Finite T] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (x y : T) (Q W : Subgroup T) (hWQ : W ≤ Q)
    (hQc : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q) (hWz : ∀ w ∈ W, ∀ g : T, g * w = w * g)
    (hc : y⁻¹ * x⁻¹ * y * x ∈ Q) (hQx : ∀ q ∈ Q, q⁻¹ * x⁻¹ * q * x ∈ W)
    (hQy : ∀ q ∈ Q, q⁻¹ * y⁻¹ * q * y ∈ W) (hxy : x ^ p * y ^ p = 1)
    (hexp : p ∣ Monoid.exponent Q) {z : T} (hz : z ∈ Q) :
    orderOf (x * y * z) ∣ Monoid.exponent Q := by
  obtain ⟨q, hq, hw⟩ := exists_pow_eq_of_relations hp hp5 x y Q W hWQ hQc hWz hc hQx hQy hxy hz
  obtain ⟨k, hk⟩ := hexp
  apply orderOf_dvd_of_pow_eq_one
  have hqE : q ^ Monoid.exponent Q = 1 := by
    have := Monoid.pow_exponent_eq_one (⟨q, hq⟩ : Q)
    exact congrArg Subtype.val this
  calc (x * y * z) ^ Monoid.exponent Q = (x * y * z) ^ (p * k) := by rw [← hk]
    _ = ((x * y * z) ^ p) ^ k := by rw [pow_mul]
    _ = (q ^ p) ^ k := by rw [hw]
    _ = q ^ Monoid.exponent Q := by rw [← pow_mul, ← hk]
    _ = 1 := hqE

theorem false_of_relations {T : Type*} [Group T] [Finite T] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (x y : T) (Q W : Subgroup T) (hWQ : W ≤ Q)
    (hQc : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q) (hWz : ∀ w ∈ W, ∀ g : T, g * w = w * g)
    (hc : y⁻¹ * x⁻¹ * y * x ∈ Q) (hQx : ∀ q ∈ Q, q⁻¹ * x⁻¹ * q * x ∈ W)
    (hQy : ∀ q ∈ Q, q⁻¹ * y⁻¹ * q * y ∈ W) (hxy : x ^ p * y ^ p = 1)
    (hexp : p ∣ Monoid.exponent Q) {z : T} (hz : z ∈ Q)
    (hord : orderOf (x * y * z) = p * Monoid.exponent Q) : False := by
  have hdvd := orderOf_dvd_exponent_of_relations hp hp5 x y Q W hWQ hQc hWz hc hQx hQy hxy hexp hz
  rw [hord] at hdvd
  have hpos : 0 < Monoid.exponent Q := Nat.pos_of_ne_zero Monoid.exponent_ne_zero_of_finite
  have := Nat.le_of_dvd hpos hdvd
  have h2 := hp.two_le
  nlinarith

theorem false_of_subgroup_relations {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (T Q W : Subgroup G) (hQT : Q ≤ T) (hWQ : W ≤ Q) (x y z : G) (hx : x ∈ T)
    (hy : y ∈ T) (hz : z ∈ Q) (hQc : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q)
    (hWz : ∀ w ∈ W, ∀ t ∈ T, t * w = w * t) (hc : y⁻¹ * x⁻¹ * y * x ∈ Q)
    (hQx : ∀ q ∈ Q, q⁻¹ * x⁻¹ * q * x ∈ W) (hQy : ∀ q ∈ Q, q⁻¹ * y⁻¹ * q * y ∈ W)
    (hxy : x ^ p * y ^ p = 1) (hexp : p ∣ Monoid.exponent Q)
    (hord : orderOf (x * y * z) = p * Monoid.exponent Q) : False := by
  have hWT : W ≤ T := hWQ.trans hQT
  have hQ'exp : Monoid.exponent (Q.subgroupOf T) = Monoid.exponent Q :=
    Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQT)
  refine false_of_relations (T := T) hp hp5 ⟨x, hx⟩ ⟨y, hy⟩ (Q.subgroupOf T) (W.subgroupOf T)
    (fun w hw => Subgroup.mem_subgroupOf.mpr (hWQ (Subgroup.mem_subgroupOf.mp hw))) ?_ ?_ ?_ ?_ ?_
    ?_ ?_ (z := ⟨z, hQT hz⟩) (Subgroup.mem_subgroupOf.mpr hz) ?_
  · intro q hq q' hq'
    exact Subtype.ext (hQc q (Subgroup.mem_subgroupOf.mp hq) q' (Subgroup.mem_subgroupOf.mp hq'))
  · intro w hw g
    exact Subtype.ext (hWz w (Subgroup.mem_subgroupOf.mp hw) g g.2)
  · exact Subgroup.mem_subgroupOf.mpr hc
  · intro q hq
    exact Subgroup.mem_subgroupOf.mpr (hQx q (Subgroup.mem_subgroupOf.mp hq))
  · intro q hq
    exact Subgroup.mem_subgroupOf.mpr (hQy q (Subgroup.mem_subgroupOf.mp hq))
  · exact Subtype.ext hxy
  · rw [hQ'exp]
    exact hexp
  · rw [hQ'exp, ← hord, ← Subgroup.orderOf_coe]
    rfl

end CFSG.RankThree.PartOne.Sec11Algebra
