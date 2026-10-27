module

public import CFSG.RankThree.PartOne.KE6.Phi3Arith
public import CFSG.RankThree.PartOne.KE6.Phi6Arith

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.KE6 (phi3_algebra prod_map_ordProj_eq_three)

@[expose] def e7T3Order (q : ℕ) (ε : ℤ) : ℕ :=
  ((q : ℤ) - ε).natAbs * (((q : ℤ) ^ 2 + ε * q + 1).natAbs) ^ 3

section Generic

variable {R : Type*} [CommRing R] [IsDomain R]

theorem orderOf_neg_of_cube_root {r : R} (hx : r ^ 2 + r + 1 = 0) (h2 : (2 : R) ≠ 0)
    (h3 : (3 : R) ≠ 0) (hr1 : r ≠ 1) : orderOf (-r) = 6 := by
  have hr3 : r ^ 3 = 1 := by linear_combination (r - 1) * hx
  have h6 : (-r) ^ 6 = 1 := by linear_combination (r ^ 3 + 1) * hr3
  refine (orderOf_eq_iff (by norm_num)).2 ⟨h6, fun m hm hm0 => ?_⟩
  interval_cases m
  · intro h
    have : r = -1 := by linear_combination -h
    rw [this] at hx
    apply one_ne_zero (α := R)
    linear_combination hx
  · intro h
    apply h3
    have : r ^ 2 = 1 := by linear_combination h
    have hr : r = -2 := by linear_combination hx - this
    rw [hr] at this
    linear_combination this
  · intro h
    apply h2
    linear_combination -h - hr3
  · intro h
    apply hr1
    have : r ^ 4 = 1 := by linear_combination h
    linear_combination this - r * hr3
  · intro h
    have hsq : r ^ 2 + 1 = 0 := by linear_combination -h - r ^ 2 * hr3
    have hr0 : r = 0 := by linear_combination hx - hsq
    rw [hr0] at hx
    apply one_ne_zero (α := R)
    linear_combination hx

theorem cube_root_data {q : R} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0)
    (hx : ((ε : R) * q) ^ 2 + (ε : R) * q + 1 = 0) :
    (ε : R) * q ≠ 1 ∧ orderOf ((ε : R) * q) = 3 ∧ orderOf q = (if ε = 1 then 3 else 6) ∧
      (ε : R) * q + 1 ≠ 0 ∧ ((ε : R) * q) ^ 3 + 1 ≠ 0 ∧
      ((ε : R) * q) ^ 6 + ((ε : R) * q) ^ 3 + 1 ≠ 0 ∧ ((ε : R) * q) ^ 6 + 1 ≠ 0 := by
  have hρ1 : (ε : R) * q ≠ 1 := fun h1 => by
    rw [h1] at hx
    apply h3
    linear_combination hx
  obtain ⟨hord, h1, h2', h3', h4'⟩ := KE6.phi3_algebra ((ε : R) * q) hx h2 h3 hρ1
  refine ⟨hρ1, hord, ?_, h1, h2', h3', h4'⟩
  rcases hε with rfl | rfl
  · simpa using hord
  · have hqρ : q = -(((-1 : ℤ) : R) * q) := by simp
    have hx' : (((-1 : ℤ) : R) * q) ^ 2 + ((-1 : ℤ) : R) * q + 1 = 0 := hx
    have := orderOf_neg_of_cube_root hx' h2 h3 hρ1
    rw [← hqρ] at this
    simpa using this

end Generic

theorem e7T3_data {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 2 + ε * q + 1) :
    ¬ p ∣ q ∧ ((ε : ZMod p) * q) ^ 2 + (ε : ZMod p) * q + 1 = 0 ∧ (ε : ZMod p) * q ≠ 1 ∧
      orderOf ((ε : ZMod p) * q) = 3 ∧ orderOf (q : ZMod p) = (if ε = 1 then 3 else 6) ∧
      ¬ (p : ℤ) ∣ (q : ℤ) - ε ∧ 7 ≤ p ∧ (ε : ZMod p) * q + 1 ≠ 0 ∧
      ((ε : ZMod p) * q) ^ 3 + 1 ≠ 0 ∧ ((ε : ZMod p) * q) ^ 6 + ((ε : ZMod p) * q) ^ 3 + 1 ≠ 0 ∧
      ((ε : ZMod p) * q) ^ 6 + 1 ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hε2 : (ε : ZMod p) ^ 2 = 1 := by
    rcases hε with rfl | rfl <;> simp
  have hx : ((ε : ZMod p) * q) ^ 2 + (ε : ZMod p) * q + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 2 + ε * q + 1) p).2 h
    push_cast at this
    linear_combination this + (q : ZMod p) ^ 2 * hε2
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast CTE6.natCast_ne_zero_of_lt (p := p) (c := 2) (by norm_num) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := by
    exact_mod_cast CTE6.natCast_ne_zero_of_lt (p := p) (c := 3) (by norm_num) (by omega)
  obtain ⟨hρ1, hord, hordq, h1, h2', h3', h4'⟩ := cube_root_data hε h2 h3 hx
  have hρ0 : (ε : ZMod p) * q ≠ 0 := fun h0 => by
    rw [h0] at hx
    simp at hx
  have hq0 : (q : ZMod p) ≠ 0 := fun h0 => hρ0 (by rw [h0, mul_zero])
  refine ⟨fun hd => hq0 ((ZMod.natCast_eq_zero_iff q p).2 hd), hx, hρ1, hord, hordq, ?_, ?_,
    h1, h2', h3', h4'⟩
  · intro hd
    have h1' : (((q : ℤ) - ε : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
    push_cast at h1'
    apply hρ1
    have hqe : (q : ZMod p) = ε := sub_eq_zero.1 h1'
    rw [hqe]
    linear_combination hε2
  · have hdvd : 3 ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hρ0
    rcases hp.eq_two_or_odd' with h | h
    · omega
    · obtain ⟨k, hk⟩ := h
      omega

theorem ordProj_card_adjointGroup_E7_three {K : Type} [Field K] [Finite K]
    {p m d₁ d₂ d₃ n₀ : ℕ} {R₁ R₂ R₃ : ℤ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ Nat.card K)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = m)
    (hd₁ : d₁ ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ))
    (hd₂ : d₂ ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ))
    (hd₃ : d₃ ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ))
    (h12 : d₁ ≠ d₂) (h13 : d₁ ≠ d₃) (h23 : d₂ ≠ d₃)
    (hrest : ∀ d ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ), d ≠ d₁ → d ≠ d₂ → d ≠ d₃ → ¬ m ∣ d)
    (hn₀ : n₀ ≠ 0) (hfac₁ : ((Nat.card K ^ d₁ - 1 : ℕ) : ℤ) = n₀ * R₁) (hR₁ : ¬ (p : ℤ) ∣ R₁)
    (hfac₂ : ((Nat.card K ^ d₂ - 1 : ℕ) : ℤ) = n₀ * R₂) (hR₂ : ¬ (p : ℤ) ∣ R₂)
    (hfac₃ : ((Nat.card K ^ d₃ - 1 : ℕ) : ℤ) = n₀ * R₃) (hR₃ : ¬ (p : ℤ) ∣ R₃) :
    ordProj[p] (Nat.card (adjointGroup .E7 K)) =
      ordProj[p] n₀ * ordProj[p] n₀ * ordProj[p] n₀ := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hdpos : ∀ d ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ), 0 < d := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    omega
  have hN : ∀ d ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ), Nat.card K ^ d - 1 ≠ 0 := by
    intro d hd
    have : 1 < Nat.card K ^ d := Nat.one_lt_pow (hdpos d hd).ne' (by omega)
    omega
  rw [(CFSG.RankThree.OrdinaryECrossPrime.ordinary_E_exact_cross_prime_order_parts hp hp3 hpq).2.1,
    prod_map_ordProj_eq_three (by omega) hord (by decide) hd₁ hd₂ hd₃ h12 h13 h23 hrest,
    CTE6.ordProj_eq_of_int_factor hn₀ (hN d₁ hd₁) hfac₁ hR₁,
    CTE6.ordProj_eq_of_int_factor hn₀ (hN d₂ hd₂) hfac₂ hR₂,
    CTE6.ordProj_eq_of_int_factor hn₀ (hN d₃ hd₃) hfac₃ hR₃]

theorem e7T3_ordProj (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (h : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) :
    p ^ (Nat.card (adjointGroup .E7 K)).factorization p =
      p ^ (e7T3Order (Nat.card K) ε).factorization p := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  set q : ℕ := Nat.card K with hqdef
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpq, hx, hρ1, hord3, hordq, hnq, -, hρ2, hρ3, hρ4, hρ5⟩ := e7T3_data hp hp3 hε h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεe : ∀ k : ℕ, ε ^ (2 * k) = 1 := fun k => by rw [pow_mul, hε2, one_pow]
  set Q : ℤ := ε * q with hQ
  have hpos : 0 < (q : ℤ) ^ 2 + ε * q + 1 := by
    have hq2' : (2 : ℤ) ≤ q := by exact_mod_cast hq2
    rcases hε with rfl | rfl <;> nlinarith
  set n₀ : ℕ := ((q : ℤ) ^ 2 + ε * q + 1).natAbs with hn₀def
  have hn₀Z : (n₀ : ℤ) = Q ^ 2 + Q + 1 := by
    rw [hn₀def, Int.natAbs_of_nonneg hpos.le, hQ]
    linear_combination hε2 * (q : ℤ) ^ 2 * (-1)
  have hn₀ : n₀ ≠ 0 := by
    intro h0
    have : (n₀ : ℤ) = 0 := by exact_mod_cast h0
    omega
  have hcast : ∀ d : ℕ, ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := fun d => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hQe : ∀ k : ℕ, Q ^ (2 * k) = (q : ℤ) ^ (2 * k) := fun k => by
    rw [hQ, mul_pow, hεe k, one_mul]
  have hnd : ∀ y : ℤ, (y : ZMod p) ≠ 0 → ¬ (p : ℤ) ∣ y := fun y hy hd =>
    hy ((ZMod.intCast_zmod_eq_zero_iff_dvd y p).2 hd)
  have hρ : ((Q : ℤ) : ZMod p) = (ε : ZMod p) * q := by rw [hQ]; push_cast; rfl
  have hρ3' : ((ε : ZMod p) * q) ^ 3 = 1 := by linear_combination ((ε : ZMod p) * q - 1) * hx
  have h3 : (3 : ZMod p) ≠ 0 := by
    exact_mod_cast CTE6.natCast_ne_zero_of_lt (p := p) (c := 3) (by norm_num) (by omega)
  have hc1 : ¬ (p : ℤ) ∣ Q - 1 := hnd _ (by
    push_cast
    rw [hρ]
    exact sub_ne_zero.2 hρ1)
  have hc2 : ¬ (p : ℤ) ∣ Q ^ 3 + 1 := hnd _ (by
    push_cast
    rw [hρ]
    exact hρ3)
  have hc3 : ¬ (p : ℤ) ∣ Q ^ 6 + 1 := hnd _ (by
    push_cast
    rw [hρ]
    exact hρ5)
  have hc4 : ¬ (p : ℤ) ∣ Q ^ 12 + Q ^ 6 + 1 := hnd _ (by
    push_cast
    rw [hρ]
    intro h0
    apply h3
    have e6 : ((ε : ZMod p) * q) ^ 6 = 1 := by linear_combination ((ε : ZMod p) * q) ^ 3 * hρ3' + hρ3'
    have e12 : ((ε : ZMod p) * q) ^ 12 = 1 := by
      linear_combination ((ε : ZMod p) * q) ^ 6 * e6 + e6
    linear_combination h0 - e12 - e6)
  have hR₁ : ¬ (p : ℤ) ∣ (Q - 1) * (Q ^ 3 + 1) := hpz.not_dvd_mul hc1 hc2
  have hR₂ : ¬ (p : ℤ) ∣ (Q - 1) * (Q ^ 3 + 1) * (Q ^ 6 + 1) := hpz.not_dvd_mul hR₁ hc3
  have hR₃ : ¬ (p : ℤ) ∣ (Q - 1) * (Q ^ 3 + 1) * (Q ^ 12 + Q ^ 6 + 1) :=
    hpz.not_dvd_mul hR₁ hc4
  have hQ6 : Q ^ 6 = (q : ℤ) ^ 6 := hQe 3
  have hQ12 : Q ^ 12 = (q : ℤ) ^ 12 := hQe 6
  have hQ18 : Q ^ 18 = (q : ℤ) ^ 18 := hQe 9
  have hpq' : ¬ p ∣ Nat.card K := hpq
  have key : ∀ m : ℕ, orderOf ((Nat.card K : ℕ) : ZMod p) = m →
      (∀ d ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ), d ≠ 6 → d ≠ 12 → d ≠ 18 → ¬ m ∣ d) →
      ordProj[p] (Nat.card (adjointGroup .E7 K)) =
        ordProj[p] n₀ * ordProj[p] n₀ * ordProj[p] n₀ := fun m hm hrest =>
    ordProj_card_adjointGroup_E7_three (K := K) (p := p) (m := m) (d₁ := 6) (d₂ := 12)
      (d₃ := 18) (n₀ := n₀) (R₁ := (Q - 1) * (Q ^ 3 + 1))
      (R₂ := (Q - 1) * (Q ^ 3 + 1) * (Q ^ 6 + 1))
      (R₃ := (Q - 1) * (Q ^ 3 + 1) * (Q ^ 12 + Q ^ 6 + 1)) hp hp3 hpq' hm (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hrest hn₀
      (by rw [hcast, hn₀Z, ← hQ6]; ring) hR₁ (by rw [hcast, hn₀Z, ← hQ12]; ring) hR₂
      (by rw [hcast, hn₀Z, ← hQ18]; ring) hR₃
  have hmain : ordProj[p] (Nat.card (adjointGroup .E7 K)) =
      ordProj[p] n₀ * ordProj[p] n₀ * ordProj[p] n₀ := by
    by_cases hε1 : ε = 1
    · refine key 3 (by rw [hordq]; simp [hε1]) ?_
      decide
    · refine key 6 (by rw [hordq]; simp [hε1]) ?_
      decide
  have hna : ((q : ℤ) - ε).natAbs ≠ 0 := by
    have hq2' : (2 : ℤ) ≤ q := by exact_mod_cast hq2
    have : (q : ℤ) - ε ≠ 0 := by rcases hε with rfl | rfl <;> omega
    exact Int.natAbs_ne_zero.2 this
  have hnp : ¬ p ∣ ((q : ℤ) - ε).natAbs := fun hd => hnq (Int.natCast_dvd.2 hd)
  have hordN : ordProj[p] (e7T3Order q ε) = ordProj[p] n₀ * ordProj[p] n₀ * ordProj[p] n₀ := by
    rw [e7T3Order, Nat.ordProj_mul p hna (pow_ne_zero 3 hn₀), CTE6.ordProj_eq_one_of_not_dvd hnp,
      one_mul, pow_succ, pow_succ, pow_one, Nat.ordProj_mul p (mul_ne_zero hn₀ hn₀) hn₀,
      Nat.ordProj_mul p hn₀ hn₀]
  rw [hmain, ← hordN]

end CFSG.RankThree.PartOne.KE
