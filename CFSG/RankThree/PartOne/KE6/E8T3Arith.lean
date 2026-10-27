module

public import CFSG.RankThree.Chevalley.CubicMonomialElementaryNine
public import CFSG.RankThree.PartOne.KE.CTCasesE6Arith
public import CFSG.RankThree.SteinbergR3EOrdinaryECrossPrimeParts

public section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.KE

@[expose] def e8T3D (ε : ℤ) (q : ℕ) : ℕ := ((q : ℤ) ^ 2 + ε * q + 1).toNat

theorem e8T3D_cast {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (q : ℕ) :
    ((e8T3D ε q : ℕ) : ℤ) = (q : ℤ) ^ 2 + ε * q + 1 := by
  have h : 0 ≤ (q : ℤ) ^ 2 + ε * q + 1 := by
    rcases hε with rfl | rfl
    · positivity
    · nlinarith [sq_nonneg ((q : ℤ) - 1), sq_nonneg (q : ℤ)]
  exact Int.toNat_of_nonneg h

theorem e8T3D_ne_zero {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (q : ℕ) : e8T3D ε q ≠ 0 := by
  intro h
  have h1 := e8T3D_cast hε q
  rw [h, Nat.cast_zero] at h1
  rcases hε with rfl | rfl
  · nlinarith [sq_nonneg (q : ℤ)]
  · nlinarith [sq_nonneg ((q : ℤ) - 1), sq_nonneg (q : ℤ)]

theorem e8T3D_odd {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (q : ℕ) : Odd (e8T3D ε q) := by
  have h := e8T3D_cast hε q
  rw [← Int.odd_coe_nat, h]
  have : (q : ℤ) ^ 2 + ε * q + 1 = (q : ℤ) * ((q : ℤ) + ε) + 1 := by ring
  rw [this]
  refine Even.add_one ?_
  rcases hε with rfl | rfl
  · exact Int.even_mul_succ_self q
  · have : (q : ℤ) * ((q : ℤ) + -1) = (q : ℤ) * ((q : ℤ) - 1) := by ring
    rw [this]
    exact Int.even_mul_pred_self q

theorem e8T3_data {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 2 + ε * q + 1) :
    ¬ p ∣ q ∧ ((ε : ZMod p) * (q : ZMod p)) ^ 2 + ((ε : ZMod p) * (q : ZMod p)) + 1 = 0 ∧
      (ε : ZMod p) * (q : ZMod p) ≠ 1 ∧ 7 ≤ p ∧
      orderOf (q : ZMod p) = (if ε = 1 then 3 else 6) := by
  have hx : (q : ZMod p) ^ 2 + (ε : ZMod p) * (q : ZMod p) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 2 + ε * q + 1) p).2 h
    push_cast at this
    exact this
  have hee : (ε : ZMod p) * (ε : ZMod p) = 1 := by
    rcases hε with rfl | rfl <;> simp
  have hx' : ((ε : ZMod p) * (q : ZMod p)) ^ 2 + ((ε : ZMod p) * (q : ZMod p)) + 1 = 0 := by
    linear_combination hx + (q : ZMod p) ^ 2 * hee
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast CTE6.natCast_ne_zero_of_lt (p := p) (c := 2) (by norm_num) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := by
    exact_mod_cast CTE6.natCast_ne_zero_of_lt (p := p) (c := 3) (by norm_num) (by omega)
  set r : ZMod p := (ε : ZMod p) * (q : ZMod p) with hr
  have hr3 : r ^ 3 = 1 := by linear_combination (r - 1) * hx'
  have hr1 : r ≠ 1 := fun h1 => by
    rw [h1] at hx'
    apply h3
    linear_combination hx'
  have hq0 : (q : ZMod p) ≠ 0 := fun h0 => by
    rw [hr, h0, mul_zero] at hx'
    apply h2
    linear_combination 2 * hx'
  have hord : orderOf (q : ZMod p) = (if ε = 1 then 3 else 6) := by
    rcases hε with rfl | rfl
    · have hrq : r = (q : ZMod p) := by simp [hr]
      show orderOf (q : ZMod p) = 3
      refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (hrq ▸ hr3) fun p' hp' hdvd => ?_
      have : p' = 3 := (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_three).1 hdvd
      subst this
      simpa [← hrq] using hr1
    · have hrq : r = -(q : ZMod p) := by simp [hr]
      show orderOf (q : ZMod p) = 6
      have hq3 : (q : ZMod p) ^ 3 = -1 := by
        have : (q : ZMod p) ^ 3 = -(r ^ 3) := by rw [hrq]; ring
        rw [this, hr3]
      have hq6 : (q : ZMod p) ^ 6 = 1 := by
        have : (q : ZMod p) ^ 6 = ((q : ZMod p) ^ 3) ^ 2 := by ring
        rw [this, hq3]; ring
      refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) hq6 fun p' hp' hdvd => ?_
      have h6 : p' = 2 ∨ p' = 3 := by
        have : p' ∣ 2 * 3 := hdvd
        rcases (Nat.Prime.dvd_mul hp').1 this with h | h
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).1 h)
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp' Nat.prime_three).1 h)
      rcases h6 with rfl | rfl
      · show (q : ZMod p) ^ 3 ≠ 1
        rw [hq3]
        intro h'
        apply h2
        linear_combination -h'
      · show (q : ZMod p) ^ 2 ≠ 1
        intro h'
        apply hr1
        have h2' : r ^ 2 = 1 := by rw [hrq]; linear_combination h'
        linear_combination hr3 - r * h2'
  refine ⟨fun hd => hq0 ((ZMod.natCast_eq_zero_iff q p).2 hd), hx', hr1, ?_, hord⟩
  have hordr : orderOf r = 3 :=
    orderOf_eq_of_pow_and_pow_div_prime (by norm_num) hr3 fun p' hp' hdvd => by
      have : p' = 3 := (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_three).1 hdvd
      subst this
      simpa using hr1
  have hr0 : r ≠ 0 := fun h0 => by
    rw [h0] at hr3
    apply h2
    linear_combination -2 * hr3
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : 3 ∣ p - 1 := hordr ▸ ZMod.orderOf_dvd_card_sub_one hr0
  rcases hp.eq_two_or_odd' with h | h
  · omega
  · obtain ⟨k, hk⟩ := h
    omega

theorem prod_map_ordProj_eq_four {p q m : ℕ} (hq : 1 ≤ q) (hord : orderOf (q : ZMod p) = m)
    {D : List ℕ} (hD : D.Nodup) {d₁ d₂ d₃ d₄ : ℕ} (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D) (hd₃ : d₃ ∈ D)
    (hd₄ : d₄ ∈ D) (h12 : d₁ ≠ d₂) (h13 : d₁ ≠ d₃) (h14 : d₁ ≠ d₄) (h23 : d₂ ≠ d₃)
    (h24 : d₂ ≠ d₄) (h34 : d₃ ≠ d₄)
    (hrest : ∀ d ∈ D, d ≠ d₁ → d ≠ d₂ → d ≠ d₃ → d ≠ d₄ → ¬ m ∣ d) :
    (D.map fun d => ordProj[p] (q ^ d - 1)).prod =
      ordProj[p] (q ^ d₁ - 1) * ordProj[p] (q ^ d₂ - 1) * ordProj[p] (q ^ d₃ - 1) *
        ordProj[p] (q ^ d₄ - 1) := by
  rw [← List.prod_map_erase _ hd₁]
  have hd₂' : d₂ ∈ D.erase d₁ := (hD.mem_erase_iff).2 ⟨h12.symm, hd₂⟩
  rw [← List.prod_map_erase _ hd₂']
  have hd₃' : d₃ ∈ (D.erase d₁).erase d₂ := ((hD.erase d₁).mem_erase_iff).2 ⟨h23.symm,
    (hD.mem_erase_iff).2 ⟨h13.symm, hd₃⟩⟩
  rw [← List.prod_map_erase _ hd₃']
  have hd₄' : d₄ ∈ ((D.erase d₁).erase d₂).erase d₃ :=
    (((hD.erase d₁).erase d₂).mem_erase_iff).2 ⟨h34.symm, ((hD.erase d₁).mem_erase_iff).2
      ⟨h24.symm, (hD.mem_erase_iff).2 ⟨h14.symm, hd₄⟩⟩⟩
  rw [← List.prod_map_erase _ hd₄']
  have h1 : (((((D.erase d₁).erase d₂).erase d₃).erase d₄).map
      fun d => ordProj[p] (q ^ d - 1)).prod = 1 := by
    refine List.prod_eq_one fun y hy => ?_
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hy
    have hDe : (D.erase d₁).Nodup := hD.erase d₁
    have hDe2 : ((D.erase d₁).erase d₂).Nodup := hDe.erase d₂
    have hDe3 : (((D.erase d₁).erase d₂).erase d₃).Nodup := hDe2.erase d₃
    rw [hDe3.mem_erase_iff, hDe2.mem_erase_iff, hDe.mem_erase_iff, hD.mem_erase_iff] at hd
    exact CTE6.ordProj_eq_one_of_not_dvd (fun h => hrest d hd.2.2.2.2 hd.2.2.2.1 hd.2.2.1 hd.2.1
      hd.1 ((CTE6.dvd_pow_sub_one_iff hq hord).1 h))
  rw [h1, mul_one]
  ring

theorem ordProj_card_adjointGroup_E8_four {K : Type} [Field K] [Finite K]
    {p m d₁ d₂ d₃ d₄ n₀ : ℕ} {R₁ R₂ R₃ R₄ : ℤ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ Nat.card K)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = m)
    (hd₁ : d₁ ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ))
    (hd₂ : d₂ ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ))
    (hd₃ : d₃ ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ))
    (hd₄ : d₄ ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ))
    (h12 : d₁ ≠ d₂) (h13 : d₁ ≠ d₃) (h14 : d₁ ≠ d₄) (h23 : d₂ ≠ d₃) (h24 : d₂ ≠ d₄)
    (h34 : d₃ ≠ d₄)
    (hrest : ∀ d ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ), d ≠ d₁ → d ≠ d₂ → d ≠ d₃ →
      d ≠ d₄ → ¬ m ∣ d)
    (hn₀ : n₀ ≠ 0) (hfac₁ : ((Nat.card K ^ d₁ - 1 : ℕ) : ℤ) = n₀ * R₁) (hR₁ : ¬ (p : ℤ) ∣ R₁)
    (hfac₂ : ((Nat.card K ^ d₂ - 1 : ℕ) : ℤ) = n₀ * R₂) (hR₂ : ¬ (p : ℤ) ∣ R₂)
    (hfac₃ : ((Nat.card K ^ d₃ - 1 : ℕ) : ℤ) = n₀ * R₃) (hR₃ : ¬ (p : ℤ) ∣ R₃)
    (hfac₄ : ((Nat.card K ^ d₄ - 1 : ℕ) : ℤ) = n₀ * R₄) (hR₄ : ¬ (p : ℤ) ∣ R₄) :
    ordProj[p] (Nat.card (adjointGroup .E8 K)) =
      ordProj[p] n₀ * ordProj[p] n₀ * ordProj[p] n₀ * ordProj[p] n₀ := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hdpos : ∀ d ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ), 0 < d := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    omega
  have hN : ∀ d ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ), Nat.card K ^ d - 1 ≠ 0 := by
    intro d hd
    have : 1 < Nat.card K ^ d := Nat.one_lt_pow (hdpos d hd).ne' (by omega)
    omega
  rw [(CFSG.RankThree.OrdinaryECrossPrime.ordinary_E_exact_cross_prime_order_parts hp hp3 hpq).2.2,
    prod_map_ordProj_eq_four (by omega) hord (by decide) hd₁ hd₂ hd₃ hd₄ h12 h13 h14 h23 h24 h34
      hrest,
    CTE6.ordProj_eq_of_int_factor hn₀ (hN d₁ hd₁) hfac₁ hR₁,
    CTE6.ordProj_eq_of_int_factor hn₀ (hN d₂ hd₂) hfac₂ hR₂,
    CTE6.ordProj_eq_of_int_factor hn₀ (hN d₃ hd₃) hfac₃ hR₃,
    CTE6.ordProj_eq_of_int_factor hn₀ (hN d₄ hd₄) hfac₄ hR₄]

theorem e8T3_factor {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q : ℕ} (hq : 1 ≤ q) (m : ℕ) :
    (((q ^ (6 * m) - 1 : ℕ) : ℤ)) = (e8T3D ε q : ℤ) *
      ((ε * q - 1) * ∑ i ∈ Finset.range (2 * m), (ε * q) ^ (3 * i)) := by
  have hq1 : 1 ≤ q ^ (6 * m) := Nat.one_le_pow _ _ hq
  rw [Nat.cast_sub hq1, Nat.cast_pow, Nat.cast_one, e8T3D_cast hε]
  have hε6 : ε ^ (6 * m) = 1 := by
    rcases hε with rfl | rfl
    · exact one_pow _
    · exact Even.neg_one_pow ⟨3 * m, by ring⟩
  have e1 : (q : ℤ) ^ (6 * m) = (ε * q) ^ (6 * m) := by rw [mul_pow, hε6, one_mul]
  have e2 : (ε * q) ^ (6 * m) = ((ε * q) ^ 3) ^ (2 * m) := by rw [← pow_mul]; ring_nf
  have hgeo := geom_sum_mul ((ε * (q : ℤ)) ^ 3) (2 * m)
  have hsum : ∑ i ∈ Finset.range (2 * m), ((ε * (q : ℤ)) ^ 3) ^ i =
      ∑ i ∈ Finset.range (2 * m), (ε * (q : ℤ)) ^ (3 * i) :=
    Finset.sum_congr rfl fun i _ => by rw [← pow_mul]
  rw [hsum] at hgeo
  have hee : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  calc (q : ℤ) ^ (6 * m) - 1 = ((ε * q) ^ 3) ^ (2 * m) - 1 := by rw [e1, e2]
    _ = (∑ i ∈ Finset.range (2 * m), (ε * (q : ℤ)) ^ (3 * i)) * ((ε * (q : ℤ)) ^ 3 - 1) := hgeo.symm
    _ = _ := by
      have : (ε * (q : ℤ)) ^ 3 - 1 = ((q : ℤ) ^ 2 + ε * q + 1) * (ε * q - 1) := by
        have : (ε * (q : ℤ)) ^ 3 - 1 = (ε * q - 1) * ((ε * q) ^ 2 + (ε * q) + 1) := by ring
        rw [this]
        have h2 : (ε * (q : ℤ)) ^ 2 = (q : ℤ) ^ 2 := by
          rw [mul_pow, sq ε]; rw [hee, one_mul]
        rw [h2]; ring
      rw [this]
      ring

theorem e8T3_cofactor {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 2 + ε * q + 1) {m : ℕ} (hm : 2 ≤ m) (hm5 : m ≤ 5) :
    ¬ (p : ℤ) ∣ ((ε * q - 1) * ∑ i ∈ Finset.range (2 * m), (ε * q) ^ (3 * i)) := by
  obtain ⟨-, hx, hr1, hp7, -⟩ := e8T3_data hε hp hp3 h
  have : Fact p.Prime := ⟨hp⟩
  intro hdvd
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdvd
  push_cast at h0
  set r : ZMod p := (ε : ZMod p) * (q : ZMod p) with hr
  have hr3 : r ^ 3 = 1 := by linear_combination (r - 1) * hx
  have hsum : ∑ i ∈ Finset.range (2 * m), r ^ (3 * i) = ((2 * m : ℕ) : ZMod p) := by
    have : ∀ i : ℕ, r ^ (3 * i) = 1 := fun i => by rw [pow_mul, hr3, one_pow]
    simp [this]
  rw [hsum] at h0
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact hr1 (sub_eq_zero.1 h1)
  · have h2 := (ZMod.natCast_eq_zero_iff (2 * m) p).1 h1
    rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
    · have := Nat.le_of_dvd (by omega) h3
      omega

theorem e8T3_ordProj {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) :
    p ^ (Nat.card (adjointGroup .E8 K)).factorization p =
      p ^ ((e8T3D ε (Nat.card K)) ^ 4).factorization p := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨hpq, -, -, hp7, hord⟩ := e8T3_data hε hp hp3 h
  set q : ℕ := Nat.card K with hqdef
  set n₀ : ℕ := e8T3D ε q with hn₀def
  have hn₀ : n₀ ≠ 0 := e8T3D_ne_zero hε q
  have hm : ∀ d₁ : ℕ, d₁ ∈ ([12, 18, 24, 30] : List ℕ) → ∃ m, d₁ = 6 * m ∧ 2 ≤ m ∧ m ≤ 5 := by
    intro d₁ hd₁
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd₁
    rcases hd₁ with rfl | rfl | rfl | rfl
    exacts [⟨2, rfl, le_rfl, by norm_num⟩, ⟨3, rfl, by norm_num, by norm_num⟩,
      ⟨4, rfl, by norm_num, by norm_num⟩, ⟨5, rfl, by norm_num, le_rfl⟩]
  have hfac : ∀ m : ℕ, ((q ^ (6 * m) - 1 : ℕ) : ℤ) = n₀ *
      ((ε * q - 1) * ∑ i ∈ Finset.range (2 * m), (ε * q) ^ (3 * i)) := fun m =>
    by rw [hn₀def]; exact e8T3_factor hε (by omega) m
  have hmod : ∀ d ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ), d ≠ 12 → d ≠ 18 → d ≠ 24 →
      d ≠ 30 → ¬ (if ε = 1 then 3 else 6 : ℕ) ∣ d := by
    intro d hd h12 h18 h24 h30
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hε with rfl | rfl
    · rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  have key := ordProj_card_adjointGroup_E8_four (K := K) (p := p) (m := if ε = 1 then 3 else 6)
    (d₁ := 12) (d₂ := 18) (d₃ := 24) (d₄ := 30) (n₀ := n₀)
    (R₁ := (ε * q - 1) * ∑ i ∈ Finset.range (2 * 2), (ε * q) ^ (3 * i))
    (R₂ := (ε * q - 1) * ∑ i ∈ Finset.range (2 * 3), (ε * q) ^ (3 * i))
    (R₃ := (ε * q - 1) * ∑ i ∈ Finset.range (2 * 4), (ε * q) ^ (3 * i))
    (R₄ := (ε * q - 1) * ∑ i ∈ Finset.range (2 * 5), (ε * q) ^ (3 * i))
    hp hp3 hpq hord (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hmod hn₀ (hfac 2)
    (e8T3_cofactor hε hp hp3 h (m := 2) (by norm_num) (by norm_num)) (hfac 3)
    (e8T3_cofactor hε hp hp3 h (m := 3) (by norm_num) (by norm_num)) (hfac 4)
    (e8T3_cofactor hε hp hp3 h (m := 4) (by norm_num) (by norm_num)) (hfac 5)
    (e8T3_cofactor hε hp hp3 h (m := 5) (by norm_num) (by norm_num))
  rw [key, show n₀ ^ 4 = n₀ * n₀ * n₀ * n₀ by ring,
    Nat.ordProj_mul p (mul_ne_zero (mul_ne_zero hn₀ hn₀) hn₀) hn₀,
    Nat.ordProj_mul p (mul_ne_zero hn₀ hn₀) hn₀, Nat.ordProj_mul p hn₀ hn₀]

end CFSG.RankThree.PartOne.KE6
