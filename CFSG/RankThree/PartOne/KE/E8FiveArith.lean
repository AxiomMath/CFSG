module

public import CFSG.RankThree.Chevalley.CubicMonomialElementaryNine
public import CFSG.RankThree.Lattice.SteinbergBIQuotient
public import CFSG.RankThree.PartOne.KE.CTCasesE6Arith
public import CFSG.RankThree.SteinbergR3EOrdinaryECrossPrimeParts

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.Lattice

namespace CTE6

theorem prod_map_ordProj_eq_two {p q m : ℕ} (hq : 1 ≤ q) (hord : orderOf (q : ZMod p) = m)
    {D : List ℕ} (hD : D.Nodup) {d₁ d₂ : ℕ} (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D) (hne : d₁ ≠ d₂)
    (hrest : ∀ d ∈ D, d ≠ d₁ → d ≠ d₂ → ¬ m ∣ d) :
    (D.map fun d => ordProj[p] (q ^ d - 1)).prod =
      ordProj[p] (q ^ d₁ - 1) * ordProj[p] (q ^ d₂ - 1) := by
  rw [← List.prod_map_erase _ hd₁]
  have hd₂' : d₂ ∈ D.erase d₁ := (hD.mem_erase_iff).2 ⟨hne.symm, hd₂⟩
  rw [← List.prod_map_erase _ hd₂']
  have h1 : (((D.erase d₁).erase d₂).map fun d => ordProj[p] (q ^ d - 1)).prod = 1 := by
    refine List.prod_eq_one fun y hy => ?_
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hy
    have hDe : (D.erase d₁).Nodup := hD.erase d₁
    rw [hDe.mem_erase_iff, hD.mem_erase_iff] at hd
    exact ordProj_eq_one_of_not_dvd (fun h => hrest d hd.2.2 hd.2.1 hd.1
      ((dvd_pow_sub_one_iff hq hord).1 h))
  rw [h1, mul_one]

end CTE6

theorem ordProj_card_adjointGroup_E8_two {K : Type} [Field K] [Finite K]
    {p m d₁ d₂ n₀ : ℕ} {R₁ R₂ : ℤ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ Nat.card K)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = m)
    (hd₁ : d₁ ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ))
    (hd₂ : d₂ ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ)) (hne : d₁ ≠ d₂)
    (hrest : ∀ d ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ), d ≠ d₁ → d ≠ d₂ → ¬ m ∣ d)
    (hn₀ : n₀ ≠ 0) (hfac₁ : ((Nat.card K ^ d₁ - 1 : ℕ) : ℤ) = n₀ * R₁) (hR₁ : ¬ (p : ℤ) ∣ R₁)
    (hfac₂ : ((Nat.card K ^ d₂ - 1 : ℕ) : ℤ) = n₀ * R₂) (hR₂ : ¬ (p : ℤ) ∣ R₂) :
    ordProj[p] (Nat.card (adjointGroup .E8 K)) = ordProj[p] n₀ * ordProj[p] n₀ := by
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
    CTE6.prod_map_ordProj_eq_two (by omega) hord (by decide) hd₁ hd₂ hne hrest,
    CTE6.ordProj_eq_of_int_factor hn₀ (hN d₁ hd₁) hfac₁ hR₁,
    CTE6.ordProj_eq_of_int_factor hn₀ (hN d₂ hd₂) hfac₂ hR₂]

namespace CTE6

theorem e8Five_zmod_facts {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (d y : ZMod p) (hd : d * d = 1)
    (hΦ : (d * y) ^ 4 + (d * y) ^ 3 + (d * y) ^ 2 + (d * y) + 1 = 0) :
    y - d ≠ 0 ∧ y ^ 5 + d ≠ 0 ∧ y ^ 10 + 1 ≠ 0 ∧ y ^ 20 + y ^ 10 + 1 ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by norm_num) (by omega)
  have h3 : ((3 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by norm_num) (by omega)
  have h5 : ((5 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by norm_num) hp5
  have hd5 : d ^ 5 = d := by
    calc d ^ 5 = (d * d) * (d * d) * d := by ring
      _ = d := by rw [hd]; ring
  have hx5 : (d * y) ^ 5 = 1 := by
    linear_combination (d * y - 1) * hΦ
  have hy5 : y ^ 5 = d := by
    have h : d * y ^ 5 = 1 := by
      calc d * y ^ 5 = (d * y) ^ 5 := by rw [mul_pow, hd5]
        _ = 1 := hx5
    calc y ^ 5 = (d * d) * y ^ 5 := by rw [hd, one_mul]
      _ = d * (d * y ^ 5) := by ring
      _ = d := by rw [h, mul_one]
  have hy10 : y ^ 10 = 1 := by
    calc y ^ 10 = (y ^ 5) ^ 2 := by ring
      _ = 1 := by rw [hy5]; linear_combination hd
  have hy20 : y ^ 20 = 1 := by
    calc y ^ 20 = (y ^ 10) ^ 2 := by ring
      _ = 1 := by rw [hy10]; ring
  have hdu : d ≠ 0 := fun h0 => by
    rw [h0] at hd
    simp at hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hyd : y = d := sub_eq_zero.1 h
    rw [hyd, hd] at hΦ
    apply h5
    push_cast
    linear_combination hΦ
  · intro h
    rw [hy5] at h
    apply h2
    have : d * ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination h
    exact (mul_eq_zero.1 this).resolve_left hdu
  · intro h
    rw [hy10] at h
    apply h2
    push_cast
    linear_combination h
  · intro h
    rw [hy20, hy10] at h
    apply h3
    push_cast
    linear_combination h

end CTE6

theorem e8Five_ordProj (K : Type) [Field K] [Finite K] (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 < p) {m : ℕ} (hm : m = 5 ∨ m = 10)
    (hordq : orderOf ((Nat.card K : ℕ) : ZMod p) = m) (hpq : ¬ p ∣ Nat.card K)
    (hΦ : (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 4 +
      (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 3 +
      (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) ^ 2 +
      (((δ : ℤ) : ZMod p) * ((Nat.card K : ℕ) : ZMod p)) + 1 = 0) :
    ordProj[p] (Nat.card (adjointGroup .E8 K)) =
      ordProj[p] ((((Nat.card K : ℤ) ^ 4 + δ * (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 +
        δ * (Nat.card K : ℤ) + 1).natAbs) ^ 2) := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq : (2 : ℤ) ≤ (Nat.card K : ℤ) := by exact_mod_cast hq2
  have hδ2 : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  set q : ℕ := Nat.card K with hqdef
  set F : ℤ := (q : ℤ) ^ 4 + δ * (q : ℤ) ^ 3 + (q : ℤ) ^ 2 + δ * (q : ℤ) + 1 with hF
  have hFpos : 0 < F := by
    have h1 : (0 : ℤ) ≤ (q : ℤ) ^ 3 * ((q : ℤ) - 1) := mul_nonneg (by positivity) (by omega)
    have h2 : (0 : ℤ) ≤ (q : ℤ) * ((q : ℤ) - 1) := mul_nonneg (by positivity) (by omega)
    have h3 : (0 : ℤ) < (q : ℤ) ^ 3 := by positivity
    rw [hF]
    rcases hδ with rfl | rfl <;> nlinarith
  set n₀ : ℕ := F.natAbs with hn₀def
  have hn₀ : (n₀ : ℤ) = F := Int.natAbs_of_nonneg hFpos.le
  have hn₀ne : n₀ ≠ 0 := Int.natAbs_ne_zero.2 hFpos.ne'
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hf1, hf2, hf3, hf4⟩ := CTE6.e8Five_zmod_facts hp hp5 ((δ : ℤ) : ZMod p)
    ((q : ℕ) : ZMod p) (by rw [← Int.cast_mul, hδ2]; simp) hΦ
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcast : ∀ d : ℕ, ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := fun d => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hnd : ∀ y : ℤ, (y : ZMod p) ≠ 0 → ¬ (p : ℤ) ∣ y := fun y hy hd =>
    hy ((ZMod.intCast_zmod_eq_zero_iff_dvd y p).2 hd)
  have hR1 : ¬ (p : ℤ) ∣ ((q : ℤ) - δ) * ((q : ℤ) ^ 5 + δ) * ((q : ℤ) ^ 10 + 1) := by
    refine hpz.not_dvd_mul (hpz.not_dvd_mul (hnd _ ?_) (hnd _ ?_)) (hnd _ ?_)
    · push_cast
      exact hf1
    · push_cast
      exact hf2
    · push_cast
      exact hf3
  have hR2 : ¬ (p : ℤ) ∣ ((q : ℤ) - δ) * ((q : ℤ) ^ 5 + δ) * ((q : ℤ) ^ 20 + (q : ℤ) ^ 10 + 1) := by
    refine hpz.not_dvd_mul (hpz.not_dvd_mul (hnd _ ?_) (hnd _ ?_)) (hnd _ ?_)
    · push_cast
      exact hf1
    · push_cast
      exact hf2
    · push_cast
      exact hf4
  have hrest : ∀ d ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ), d ≠ 20 → d ≠ 30 → ¬ m ∣ d := by
    intro d hd h20 h30
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hm with rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have key := ordProj_card_adjointGroup_E8_two (K := K) (p := p) (m := m) (d₁ := 20) (d₂ := 30)
    (n₀ := n₀) (R₁ := ((q : ℤ) - δ) * ((q : ℤ) ^ 5 + δ) * ((q : ℤ) ^ 10 + 1))
    (R₂ := ((q : ℤ) - δ) * ((q : ℤ) ^ 5 + δ) * ((q : ℤ) ^ 20 + (q : ℤ) ^ 10 + 1)) hp
    (by omega) hpq hordq (by decide) (by decide) (by decide) hrest hn₀ne
    (by rw [hcast, hn₀, hF]; rcases hδ with rfl | rfl <;> ring) hR1
    (by rw [hcast, hn₀, hF]; rcases hδ with rfl | rfl <;> ring) hR2
  rw [key, sq, Nat.ordProj_mul p hn₀ne hn₀ne]

end CFSG.RankThree.PartOne.KE
