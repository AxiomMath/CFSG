module

public import CFSG.RankThree.PartOne.KE.E6FourArith

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.Lattice

theorem ordProj_card_adjointGroup_E7_two {K : Type} [Field K] [Finite K]
    {p m d₁ d₂ n₀ : ℕ} {R₁ R₂ : ℤ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ Nat.card K)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = m)
    (hd₁ : d₁ ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ))
    (hd₂ : d₂ ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ)) (hne : d₁ ≠ d₂)
    (hrest : ∀ d ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ), d ≠ d₁ → d ≠ d₂ → ¬ m ∣ d)
    (hn₀ : n₀ ≠ 0) (hfac₁ : ((Nat.card K ^ d₁ - 1 : ℕ) : ℤ) = n₀ * R₁) (hR₁ : ¬ (p : ℤ) ∣ R₁)
    (hfac₂ : ((Nat.card K ^ d₂ - 1 : ℕ) : ℤ) = n₀ * R₂) (hR₂ : ¬ (p : ℤ) ∣ R₂) :
    ordProj[p] (Nat.card (adjointGroup .E7 K)) = ordProj[p] n₀ * ordProj[p] n₀ := by
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
    CTE6.prod_map_ordProj_eq_two (by omega) hord (by decide) hd₁ hd₂ hne hrest,
    CTE6.ordProj_eq_of_int_factor hn₀ (hN d₁ hd₁) hfac₁ hR₁,
    CTE6.ordProj_eq_of_int_factor hn₀ (hN d₂ hd₂) hfac₂ hR₂]

theorem not_dvd_of_mod_ne {p : ℕ} {m R g c : ℤ} (hm : (p : ℤ) ∣ m) (hR : R = m * g + c)
    (hc0 : c ≠ 0) (hcp : c.natAbs < p) : ¬ (p : ℤ) ∣ R := by
  intro h
  have h1 : (p : ℤ) ∣ c := by
    have : c = R - m * g := by rw [hR]; ring
    rw [this]
    exact dvd_sub h (dvd_mul_of_dvd_left hm g)
  have h2 : p ∣ c.natAbs := Int.natCast_dvd.1 h1
  exact absurd (Nat.le_of_dvd (Int.natAbs_pos.2 hc0) h2) (by omega)

theorem e7F4_ordProj {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1) :
    ordProj[p] (Nat.card (adjointGroup .E7 K)) = ordProj[p] ((Nat.card K ^ 2 + 1) ^ 2) := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  set q : ℕ := Nat.card K with hqdef
  obtain ⟨hpq, hord, -, -⟩ := e6Four_data hp hp3 hpf
  have hn₀ : q ^ 2 + 1 ≠ 0 := by positivity
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcast : ∀ d : ℕ, ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := fun d => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hn₀Z : (((q ^ 2 + 1 : ℕ)) : ℤ) = (q : ℤ) ^ 2 + 1 := by
    push_cast
    ring
  have hA : ¬ (p : ℤ) ∣ (q : ℤ) ^ 2 - 1 :=
    not_dvd_of_mod_ne (g := 1) (c := -2) hpf (by ring) (by norm_num) (by simp; omega)
  have hB : ¬ (p : ℤ) ∣ (q : ℤ) ^ 4 + 1 :=
    not_dvd_of_mod_ne (g := (q : ℤ) ^ 2 - 1) (c := 2) hpf (by ring) (by norm_num) (by simp; omega)
  have hC : ¬ (p : ℤ) ∣ (q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1 :=
    not_dvd_of_mod_ne (g := ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 4 + 2)) (c := 3) hpf (by ring)
      (by norm_num) (by simp; omega)
  have hR₁ : ¬ (p : ℤ) ∣ ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 4 + 1) := fun h =>
    (hpz.dvd_or_dvd h).elim hA hB
  have hR₂ : ¬ (p : ℤ) ∣ ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1) := fun h =>
    (hpz.dvd_or_dvd h).elim hA hC
  have hrest : ∀ d ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ), d ≠ 8 → d ≠ 12 → ¬ 4 ∣ d := by
    decide
  have key := ordProj_card_adjointGroup_E7_two (K := K) (p := p) (m := 4) (d₁ := 8) (d₂ := 12)
    (n₀ := q ^ 2 + 1) (R₁ := ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 4 + 1))
    (R₂ := ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1)) hp hp3 hpq hord (by decide)
    (by decide) (by decide) hrest hn₀ (by rw [hcast, hn₀Z]; ring) hR₁
    (by rw [hcast, hn₀Z]; ring) hR₂
  rw [key, pow_two (q ^ 2 + 1), Nat.ordProj_mul p hn₀ hn₀]

end CFSG.RankThree.PartOne.KE
