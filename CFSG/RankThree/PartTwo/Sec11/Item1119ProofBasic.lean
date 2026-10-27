module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Proof

open scoped commutatorElement

section Arithmetic

theorem three_pow_dvd_three_mul_sub_one {j : ℕ} {k : ℤ} (h : (3 : ℤ) ^ j ∣ k ^ 3 - 1) :
    (3 : ℤ) ^ j ∣ 3 * (k - 1) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : (3 : ℤ) ∣ k ^ 3 - 1 := (dvd_pow_self 3 hj.ne').trans h
  have hk : (3 : ℤ) ∣ k - 1 := by
    have h1 : ((k ^ 3 - 1 : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h3
    have h2 : ((k : ZMod 3)) ^ 3 = (k : ZMod 3) := ZMod.pow_card (k : ZMod 3)
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
    push_cast at h1 ⊢
    rw [h2] at h1
    exact h1
  obtain ⟨t, ht⟩ := hk
  have hkt : k = 3 * t + 1 := by linarith
  subst hkt
  have e1 : (3 * t + 1) ^ 3 - 1 = 9 * t * (3 * t ^ 2 + 3 * t + 1) := by ring
  have e2 : 3 * (3 * t + 1 - 1) = 9 * t := by ring
  rw [e1] at h
  rw [e2]
  have hcop : IsCoprime ((3 : ℤ) ^ j) (3 * t ^ 2 + 3 * t + 1) :=
    IsCoprime.pow_left ⟨-(t ^ 2 + t), 1, by ring⟩
  exact hcop.dvd_of_dvd_mul_right h

theorem three_dvd_sub_one_of_dvd_pow {e : ℕ} {k : ℤ} (h : (3 : ℤ) ∣ k ^ 3 ^ e - 1) :
    (3 : ℤ) ∣ k - 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : ((k ^ 3 ^ e - 1 : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h
  have h2 : ((k : ZMod 3)) ^ 3 ^ e = (k : ZMod 3) := ZMod.pow_card_pow (k : ZMod 3)
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
  push_cast at h1 ⊢
  rw [h2] at h1
  exact h1

end Arithmetic

section Elementary

variable {G : Type*} [Group G]

theorem pow_conj_eq_zpow_pow {x y : G} {k : ℤ} (hk : y * x * y⁻¹ = x ^ k) (n : ℕ) :
    y ^ n * x * (y ^ n)⁻¹ = x ^ (k ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc y ^ (n + 1) * x * (y ^ (n + 1))⁻¹ = y * (y ^ n * x * (y ^ n)⁻¹) * y⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          group
      _ = (y * x * y⁻¹) ^ (k ^ n) := by rw [ih, conj_zpow]
      _ = x ^ (k ^ (n + 1)) := by rw [hk, ← zpow_mul, pow_succ, mul_comm]

theorem exists_orderOf_eq_three_pow' {x : G} (hx : ∃ n : ℕ, x ^ 3 ^ n = 1) :
    ∃ j : ℕ, orderOf x = 3 ^ j := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hn)
  exact ⟨j, hj⟩

theorem exists_conj_eq_zpow_one_add_three_mul {x y : G} (hx : ∃ n : ℕ, x ^ 3 ^ n = 1)
    (hy : ∃ n : ℕ, y ^ 3 ^ n = 1) (hyx : y * x * y⁻¹ ∈ Subgroup.zpowers x) :
    ∃ t : ℤ, y * x * y⁻¹ = x ^ (1 + 3 * t) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyx
  obtain ⟨e, he⟩ := hy
  obtain ⟨j, hj⟩ := exists_orderOf_eq_three_pow' hx
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have hx1 : x = 1 := orderOf_eq_one_iff.mp (by rw [hj, pow_zero])
    exact ⟨0, by rw [hx1]; simp⟩
  have h1 := pow_conj_eq_zpow_pow hk.symm (3 ^ e)
  rw [he, one_mul, inv_one, mul_one] at h1
  have h2 : x ^ (k ^ 3 ^ e - 1) = 1 := by
    rw [zpow_sub_one, ← h1]
    exact mul_inv_cancel x
  have h3 : ((orderOf x : ℕ) : ℤ) ∣ k ^ 3 ^ e - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h2
  rw [hj] at h3
  push_cast at h3
  obtain ⟨t, ht⟩ := three_dvd_sub_one_of_dvd_pow ((dvd_pow_self 3 hj0.ne').trans h3)
  exact ⟨t, by rw [← hk, show 1 + 3 * t = k by linarith]⟩

theorem conj_mem_zpowers_of_mem_normalizer {x y : G}
    (hyN : y ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G)) :
    y * x * y⁻¹ ∈ Subgroup.zpowers x :=
  (Subgroup.mem_normalizer_iff.mp hyN x).mp (Subgroup.mem_zpowers x)

theorem conj_mul_inv_mem_zpowers_pow_three {x y : G} (hx : ∃ n : ℕ, x ^ 3 ^ n = 1)
    (hy : ∃ n : ℕ, y ^ 3 ^ n = 1) (hyN : y ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G)) :
    y * x * y⁻¹ * x⁻¹ ∈ Subgroup.zpowers (x ^ 3) := by
  obtain ⟨t, ht⟩ :=
    exists_conj_eq_zpow_one_add_three_mul hx hy (conj_mem_zpowers_of_mem_normalizer hyN)
  refine Subgroup.mem_zpowers_iff.mpr ⟨t, ?_⟩
  rw [ht, ← zpow_natCast x 3, ← zpow_mul, ← zpow_sub_one, add_sub_cancel_left]
  norm_num

theorem inv_pow_three_mul_conj_mem_zpowers_pow_nine {x y : G} (hx : ∃ n : ℕ, x ^ 3 ^ n = 1)
    (hy : ∃ n : ℕ, y ^ 3 ^ n = 1) (hyN : y ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G)) :
    (x ^ 3)⁻¹ * y⁻¹ * x ^ 3 * y ∈ Subgroup.zpowers (x ^ 9) := by
  have hy' : ∃ n : ℕ, y⁻¹ ^ 3 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hy
    exact ⟨n, by rw [inv_pow, hn, inv_one]⟩
  obtain ⟨t, ht⟩ := exists_conj_eq_zpow_one_add_three_mul hx hy'
    (conj_mem_zpowers_of_mem_normalizer (Subgroup.inv_mem _ hyN))
  rw [inv_inv] at ht
  have e : (x ^ 3)⁻¹ * y⁻¹ * x ^ 3 * y = (x ^ 3)⁻¹ * (y⁻¹ * x * y) ^ 3 := by
    rw [show (y⁻¹ * x * y) ^ 3 = y⁻¹ * x ^ 3 * y by
      simpa using (conj_pow (a := y⁻¹) (b := x) (i := 3))]
    group
  rw [e, ht, ← zpow_natCast x 3, ← zpow_natCast (x ^ (1 + 3 * t)) 3, ← zpow_mul,
    ← zpow_neg, ← zpow_add]
  refine Subgroup.mem_zpowers_iff.mpr ⟨t, ?_⟩
  rw [← zpow_natCast x 9, ← zpow_mul]
  congr 1
  push_cast
  ring

theorem conj_pow_three_eq_of_pow_three_eq_one {a x : G} (ha : a ^ 3 = 1)
    (hx : ∃ n : ℕ, x ^ 3 ^ n = 1) (haN : a ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G)) :
    a * x ^ 3 * a⁻¹ = x ^ 3 ∧ (a * x * a⁻¹ * x⁻¹) ^ 3 = 1 := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (conj_mem_zpowers_of_mem_normalizer haN)
  obtain ⟨j, hj⟩ := exists_orderOf_eq_three_pow' hx
  have h1 := pow_conj_eq_zpow_pow hk.symm 3
  rw [ha, one_mul, inv_one, mul_one] at h1
  have h2 : x ^ (k ^ 3 - 1) = 1 := by
    rw [zpow_sub_one, ← h1]
    exact mul_inv_cancel x
  have h3 : ((orderOf x : ℕ) : ℤ) ∣ k ^ 3 - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h2
  rw [hj] at h3
  push_cast at h3
  have h4 := three_pow_dvd_three_mul_sub_one h3
  have h5 : x ^ (3 * (k - 1)) = 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.mp
    rw [hj]
    push_cast
    exact h4
  constructor
  · calc a * x ^ 3 * a⁻¹ = (a * x * a⁻¹) ^ 3 := by rw [conj_pow]
      _ = x ^ 3 * x ^ (3 * (k - 1)) := by
          rw [← hk, ← zpow_natCast (x ^ k) 3, ← zpow_mul, ← zpow_natCast x 3, ← zpow_add]
          congr 1
          push_cast
          ring
      _ = x ^ 3 := by rw [h5, mul_one]
  · rw [← hk, ← zpow_sub_one, ← zpow_natCast (x ^ (k - 1)) 3, ← zpow_mul]
    rw [show (k - 1) * ((3 : ℕ) : ℤ) = 3 * (k - 1) by push_cast; ring]
    exact h5

theorem exists_zpow_mul_of_mem_sup {w : G} {M : Subgroup G}
    (hw : w ∈ Subgroup.normalizer (M : Set G)) {y : G} (hy : y ∈ Subgroup.zpowers w ⊔ M) :
    ∃ k : ℤ, ∃ m ∈ M, y = w ^ k * m := by
  have hle : Subgroup.zpowers w ≤ Subgroup.normalizer (M : Set G) := Subgroup.zpowers_le.mpr hw
  have hy' : y ∈ ((Subgroup.zpowers w ⊔ M : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hy'
  obtain ⟨u, hu, m, hm, rfl⟩ := Set.mem_mul.mp hy'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  exact ⟨k, m, hm, rfl⟩

theorem mem_normalizer_sup {w : G} {H K : Subgroup G} (hH : w ∈ Subgroup.normalizer (H : Set G))
    (hK : w ∈ Subgroup.normalizer (K : Set G)) :
    w ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem commutator_mem_of_mem_closure {t : G} {N : Subgroup G} {S : Set G}
    (hSN : Subgroup.closure S ≤ Subgroup.normalizer (N : Set G))
    (hS : ∀ w ∈ S, t * w * t⁻¹ * w⁻¹ ∈ N) {w : G} (hw : w ∈ Subgroup.closure S) :
    t * w * t⁻¹ * w⁻¹ ∈ N := by
  induction hw using Subgroup.closure_induction with
  | mem w hw => exact hS w hw
  | one => simp
  | mul w₁ w₂ hw₁ _ h₁ h₂ =>
    have e : t * (w₁ * w₂) * t⁻¹ * (w₁ * w₂)⁻¹ =
        (t * w₁ * t⁻¹ * w₁⁻¹) * (w₁ * (t * w₂ * t⁻¹ * w₂⁻¹) * w₁⁻¹) := by group
    rw [e]
    exact N.mul_mem h₁ ((Subgroup.mem_normalizer_iff.mp (hSN hw₁) _).mp h₂)
  | inv w hw' h₁ =>
    have e : t * w⁻¹ * t⁻¹ * w⁻¹⁻¹ = w⁻¹ * (t * w * t⁻¹ * w⁻¹)⁻¹ * w⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hSN hw')) _).mp (N.inv_mem h₁)

theorem zpow_conj_eq_zpow_mul {t a z : G} (htz : t * z = z * t)
    (hta : t * a * t⁻¹ = z * a) (n : ℤ) : t ^ n * a * (t ^ n)⁻¹ = z ^ n * a := by
  have htz' : Commute t z := htz
  have hinv : t⁻¹ * a * t = z⁻¹ * a := by
    have h1 : t * (z⁻¹ * a) * t⁻¹ = a := by
      have e : t * (z⁻¹ * a) * t⁻¹ = (t * z⁻¹ * t⁻¹) * (t * a * t⁻¹) := by group
      rw [e, hta, show t * z⁻¹ * t⁻¹ = z⁻¹ by rw [(htz'.inv_right).eq, mul_inv_cancel_right]]
      group
    calc t⁻¹ * a * t = t⁻¹ * (t * (z⁻¹ * a) * t⁻¹) * t := by rw [h1]
      _ = z⁻¹ * a := by group
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    calc t ^ ((i : ℤ) + 1) * a * (t ^ ((i : ℤ) + 1))⁻¹
        = t ^ (i : ℤ) * (t * a * t⁻¹) * (t ^ (i : ℤ))⁻¹ := by rw [zpow_add_one]; group
      _ = (t ^ (i : ℤ) * z * (t ^ (i : ℤ))⁻¹) * (t ^ (i : ℤ) * a * (t ^ (i : ℤ))⁻¹) := by
          rw [hta]; group
      _ = z * (z ^ (i : ℤ) * a) := by
          rw [ih, (htz'.zpow_left (i : ℤ)).eq, mul_inv_cancel_right]
      _ = z ^ ((i : ℤ) + 1) * a := by
          rw [zpow_add_one, ← mul_assoc, (Commute.self_zpow z (i : ℤ)).eq]
  | pred i ih =>
    calc t ^ (-(i : ℤ) - 1) * a * (t ^ (-(i : ℤ) - 1))⁻¹
        = t ^ (-(i : ℤ)) * (t⁻¹ * a * t) * (t ^ (-(i : ℤ)))⁻¹ := by rw [zpow_sub_one]; group
      _ = (t ^ (-(i : ℤ)) * z⁻¹ * (t ^ (-(i : ℤ)))⁻¹) *
            (t ^ (-(i : ℤ)) * a * (t ^ (-(i : ℤ)))⁻¹) := by rw [hinv]; group
      _ = z⁻¹ * (z ^ (-(i : ℤ)) * a) := by
          rw [ih, ((htz'.inv_right).zpow_left (-(i : ℤ))).eq, mul_inv_cancel_right]
      _ = z ^ (-(i : ℤ) - 1) * a := by
          rw [zpow_sub_one, ← mul_assoc, (Commute.self_zpow z (-(i : ℤ))).inv_left.eq]

theorem mem_secondCenter_iff {P : Subgroup G} {y : G} :
    y ∈ (Subgroup.upperCentralSeries P 2).map P.subtype ↔
      y ∈ P ∧ ∀ p ∈ P, ∀ q ∈ P, q * ⁅y, p⁆ = ⁅y, p⁆ * q := by
  have key : ∀ y' : P, y' ∈ Subgroup.upperCentralSeries P 2 ↔
      ∀ p' : P, ⁅y', p'⁆ ∈ Subgroup.center P := by
    intro y'
    rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff,
      Subgroup.upperCentralSeries_one]
  constructor
  · rintro ⟨y', hy', rfl⟩
    refine ⟨y'.2, fun p hp q hq => ?_⟩
    have h := Subgroup.mem_center_iff.mp ((key y').mp hy' ⟨p, hp⟩) ⟨q, hq⟩
    have h' := congrArg Subtype.val h
    simpa [commutatorElement_def] using h'
  · rintro ⟨hyP, hy⟩
    refine ⟨⟨y, hyP⟩, (key _).mpr fun p' => Subgroup.mem_center_iff.mpr fun q' => ?_, rfl⟩
    apply Subtype.ext
    have h := hy p' p'.2 q' q'.2
    simpa [commutatorElement_def] using h

theorem conj_mem_secondCenter {P : Subgroup G} {n y : G}
    (hn : n ∈ Subgroup.normalizer (P : Set G))
    (hy : y ∈ (Subgroup.upperCentralSeries P 2).map P.subtype) :
    n * y * n⁻¹ ∈ (Subgroup.upperCentralSeries P 2).map P.subtype := by
  rw [mem_secondCenter_iff] at hy ⊢
  obtain ⟨hyP, hy⟩ := hy
  have hconj : ∀ z ∈ P, n⁻¹ * z * n ∈ P := fun z hz => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) z).mp hz
    rwa [inv_inv] at this
  refine ⟨(Subgroup.mem_normalizer_iff.mp hn y).mp hyP, fun p hp q hq => ?_⟩
  have h := hy _ (hconj p hp) _ (hconj q hq)
  have e1 : q * ⁅n * y * n⁻¹, p⁆ = n * ((n⁻¹ * q * n) * ⁅y, n⁻¹ * p * n⁆) * n⁻¹ := by
    simp only [commutatorElement_def]
    group
  have e2 : ⁅n * y * n⁻¹, p⁆ * q = n * (⁅y, n⁻¹ * p * n⁆ * (n⁻¹ * q * n)) * n⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e1, e2, h]

theorem mem_secondCenter_of_mem_center {P : Subgroup G} {z : G} (hzP : z ∈ P)
    (hz : ∀ q ∈ P, q * z = z * q) :
    z ∈ (Subgroup.upperCentralSeries P 2).map P.subtype := by
  refine mem_secondCenter_iff.mpr ⟨hzP, fun p hp q _ => ?_⟩
  have h1 : ⁅z, p⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (hz p hp).symm
  rw [h1, mul_one, one_mul]

theorem commutator_central_of_mem_secondCenter {P : Subgroup G} {y : G}
    (hy : y ∈ (Subgroup.upperCentralSeries P 2).map P.subtype) {p : G} (hp : p ∈ P) :
    ∀ q ∈ P, q * ⁅y, p⁆ = ⁅y, p⁆ * q :=
  (mem_secondCenter_iff.mp hy).2 p hp

end Elementary

end CFSG.RankThree.PartTwo.Sec11.Item1119Proof
