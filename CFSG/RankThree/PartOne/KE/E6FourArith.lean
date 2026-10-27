module

public import CFSG.RankThree.PartOne.KE.E8FiveArith
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.Lattice

theorem ordProj_card_adjointGroup_E6_two {K : Type} [Field K] [Finite K]
    {p m d₁ d₂ n₀ : ℕ} {R₁ R₂ : ℤ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ Nat.card K)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = m)
    (hd₁ : d₁ ∈ ([2, 5, 6, 8, 9, 12] : List ℕ))
    (hd₂ : d₂ ∈ ([2, 5, 6, 8, 9, 12] : List ℕ)) (hne : d₁ ≠ d₂)
    (hrest : ∀ d ∈ ([2, 5, 6, 8, 9, 12] : List ℕ), d ≠ d₁ → d ≠ d₂ → ¬ m ∣ d)
    (hn₀ : n₀ ≠ 0) (hfac₁ : ((Nat.card K ^ d₁ - 1 : ℕ) : ℤ) = n₀ * R₁) (hR₁ : ¬ (p : ℤ) ∣ R₁)
    (hfac₂ : ((Nat.card K ^ d₂ - 1 : ℕ) : ℤ) = n₀ * R₂) (hR₂ : ¬ (p : ℤ) ∣ R₂) :
    ordProj[p] (Nat.card (adjointGroup .E6 K)) = ordProj[p] n₀ * ordProj[p] n₀ := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hdpos : ∀ d ∈ ([2, 5, 6, 8, 9, 12] : List ℕ), 0 < d := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    omega
  have hN : ∀ d ∈ ([2, 5, 6, 8, 9, 12] : List ℕ), Nat.card K ^ d - 1 ≠ 0 := by
    intro d hd
    have : 1 < Nat.card K ^ d := Nat.one_lt_pow (hdpos d hd).ne' (by omega)
    omega
  rw [(CFSG.RankThree.OrdinaryECrossPrime.ordinary_E_exact_cross_prime_order_parts hp hp3 hpq).1,
    CTE6.prod_map_ordProj_eq_two (by omega) hord (by decide) hd₁ hd₂ hne hrest,
    CTE6.ordProj_eq_of_int_factor hn₀ (hN d₁ hd₁) hfac₁ hR₁,
    CTE6.ordProj_eq_of_int_factor hn₀ (hN d₂ hd₂) hfac₂ hR₂]

theorem e6Four_data {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : (p : ℤ) ∣ (q : ℤ) ^ 2 + 1) :
    ¬ p ∣ q ∧ orderOf (q : ZMod p) = 4 ∧ (q : ZMod p) ^ 2 + 1 = 0 ∧
      ¬ (p : ℤ) ∣ (q : ℤ) - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx : (q : ZMod p) ^ 2 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 2 + 1) p).2 h
    simpa using this
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := CTE6.natCast_ne_zero_of_lt (by norm_num) (by omega)
  have hq1 : (q : ZMod p) ^ 2 ≠ 1 := fun h1 => h2 (by push_cast; linear_combination hx - h1)
  have hq4 : (q : ZMod p) ^ 4 = 1 := by linear_combination ((q : ZMod p) ^ 2 - 1) * hx
  refine ⟨?_, ?_, hx, ?_⟩
  · intro hdvd
    have hq0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 hdvd
    rw [hq0] at hx
    simp at hx
  · have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := (q : ZMod p))
      (by simpa using hq1) (by simpa using hq4)
    simpa using this
  · intro hd
    have h1 : (((q : ℤ) - 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
    push_cast at h1
    exact hq1 (by rw [sub_eq_zero.1 h1, one_pow])

theorem e6Four_ordProj (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1) :
    p ^ (Nat.card (adjointGroup .E6 K)).factorization p =
      p ^ (((Nat.card K : ℤ) ^ 3 - (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) - 1).natAbs ^ 2
        ).factorization p := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq : (2 : ℤ) ≤ (Nat.card K : ℤ) := by exact_mod_cast hq2
  obtain ⟨hpq, hord, hx, hq1⟩ := e6Four_data hp hp3 h
  set q : ℕ := Nat.card K with hqdef
  have : Fact p.Prime := ⟨hp⟩
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set F : ℤ := (q : ℤ) ^ 3 - (q : ℤ) ^ 2 + (q : ℤ) - 1 with hF
  have hFfac : F = ((q : ℤ) ^ 2 + 1) * ((q : ℤ) - 1) := by rw [hF]; ring
  have hFpos : 0 < F := by
    rw [hFfac]
    exact mul_pos (by positivity) (by omega)
  set N : ℕ := F.natAbs with hNdef
  have hNF : (N : ℤ) = F := Int.natAbs_of_nonneg hFpos.le
  have hN0 : N ≠ 0 := Int.natAbs_ne_zero.2 hFpos.ne'
  set n₀ : ℕ := q ^ 2 + 1 with hn₀def
  have hn₀ : n₀ ≠ 0 := Nat.succ_ne_zero _
  have hn₀Z : (n₀ : ℤ) = (q : ℤ) ^ 2 + 1 := by simp [hn₀def]
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := CTE6.natCast_ne_zero_of_lt (by norm_num) (by omega)
  have h3 : ((3 : ℕ) : ZMod p) ≠ 0 := CTE6.natCast_ne_zero_of_lt (by norm_num) (by omega)
  have hy4 : (q : ZMod p) ^ 4 = 1 := by linear_combination ((q : ZMod p) ^ 2 - 1) * hx
  have hy8 : (q : ZMod p) ^ 8 = 1 := by linear_combination ((q : ZMod p) ^ 4 + 1) * hy4
  have f1 : (q : ZMod p) ^ 2 - 1 ≠ 0 := fun hc => h2 (by push_cast; linear_combination hx - hc)
  have f2 : (q : ZMod p) ^ 4 + 1 ≠ 0 := fun hc => h2 (by push_cast; linear_combination hc - hy4)
  have f3 : (q : ZMod p) ^ 8 + (q : ZMod p) ^ 4 + 1 ≠ 0 := fun hc =>
    h3 (by push_cast; linear_combination hc - hy8 - hy4)
  have hnd : ∀ y : ℤ, (y : ZMod p) ≠ 0 → ¬ (p : ℤ) ∣ y := fun y hy hd =>
    hy ((ZMod.intCast_zmod_eq_zero_iff_dvd y p).2 hd)
  have hR1 : ¬ (p : ℤ) ∣ ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 4 + 1) := by
    refine hpz.not_dvd_mul (hnd _ ?_) (hnd _ ?_)
    · push_cast
      exact f1
    · push_cast
      exact f2
  have hR2 : ¬ (p : ℤ) ∣ ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1) := by
    refine hpz.not_dvd_mul (hnd _ ?_) (hnd _ ?_)
    · push_cast
      exact f1
    · push_cast
      exact f3
  have hcast : ∀ d : ℕ, ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := fun d => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hrest : ∀ d ∈ ([2, 5, 6, 8, 9, 12] : List ℕ), d ≠ 8 → d ≠ 12 → ¬ 4 ∣ d := by
    intro d hd h8 h12
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    omega
  have key := ordProj_card_adjointGroup_E6_two (K := K) (p := p) (m := 4) (d₁ := 8) (d₂ := 12)
    (n₀ := n₀) (R₁ := ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 4 + 1))
    (R₂ := ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1)) hp hp3 hpq hord
    (by decide) (by decide) (by decide) hrest hn₀
    (by rw [hcast, hn₀Z]; ring) hR1 (by rw [hcast, hn₀Z]; ring) hR2
  have hordN : ordProj[p] N = ordProj[p] n₀ :=
    CTE6.ordProj_eq_of_int_factor hn₀ hN0 (by rw [hNF, hFfac, hn₀Z]) hq1
  rw [key, sq, Nat.ordProj_mul p hN0 hN0, hordN]

end CFSG.RankThree.PartOne.KE
