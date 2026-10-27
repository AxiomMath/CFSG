module

public import CFSG.Quasithin.H13.GoldschmidtC137SQSimp

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ

theorem card_sylow_seven {Y : Type} [Group Y] [Finite Y] (hcard : Nat.card Y = 6048)
    (P : Sylow 7 Y) : Nat.card P = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [Sylow.card_eq_multiplicity, hcard, show (6048 : ℕ) = 7 * 864 by rfl,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem sylow_seven_count_cases {n : ℕ} (hdvd : n ∣ 864) (hmod : n % 7 = 1) :
    n = 1 ∨ n = 8 ∨ n = 36 ∨ n = 288 := by
  have key : ∀ m ∈ Nat.divisors 864, m % 7 = 1 → m = 1 ∨ m = 8 ∨ m = 36 ∨ m = 288 := by
    decide +kernel
  exact key n (Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩) hmod

theorem exists_involution_centralizing {Y : Type} [Group Y] [Finite Y] (P : Subgroup Y)
    (hP : Nat.card P = 7) (hN : Nat.card (Subgroup.normalizer (P : Set Y)) = 168) :
    ∃ u : Y, orderOf u = 2 ∧ ∀ x ∈ P, u * x = x * u := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set N : Subgroup Y := Subgroup.normalizer (P : Set Y) with hNdef
  have hPN : P ≤ N := Subgroup.le_normalizer
  have hnorm : (P.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPN).2 le_rfl
  have hPc : Nat.card (P.subgroupOf N) = 7 := by
    rw [← hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv
  have : IsCyclic (P.subgroupOf N) := isCyclic_of_prime_card hPc
  let φ : N →* MulAut (P.subgroupOf N) := MulAut.conjNormal
  have hmul : Nat.card N = Nat.card φ.range * Nat.card φ.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rwa [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
  have hrange : Nat.card φ.range ∣ 6 := by
    have h1 : Nat.card φ.range ∣ Nat.card (MulAut (P.subgroupOf N)) :=
      Subgroup.card_subgroup_dvd_card φ.range
    rwa [IsCyclic.card_mulAut, hPc, show Nat.totient 7 = 6 by decide] at h1
  have heven : 2 ∣ Nat.card φ.ker := by
    have hle : Nat.card φ.range ≤ 6 := Nat.le_of_dvd (by norm_num) hrange
    have hpos : 0 < Nat.card φ.range := Nat.card_pos
    rw [hN] at hmul
    interval_cases h : Nat.card φ.range <;> omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := φ.ker) 2 heven
  refine ⟨x.1.1, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  · intro y hy
    have hk : φ x.1 = 1 := x.2
    have key := DFunLike.congr_fun hk ⟨⟨y, hPN hy⟩, (Subgroup.mem_subgroupOf).2 hy⟩
    have key2 := congrArg (fun z : ↥(P.subgroupOf N) => (((z : N) : Y))) key
    simp only [MulAut.one_apply] at key2
    change (x.1 : N).1 * y * ((x.1 : N).1)⁻¹ = y at key2
    rw [mul_inv_eq_iff_eq_mul] at key2
    exact key2

theorem card_normalizer_seven {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hcard : Nat.card Y = 6048)
    (hnc : ∀ t b : Y, orderOf t = 2 → orderOf b = 7 → t * b ≠ b * t) (P : Sylow 7 Y) :
    Nat.card (Subgroup.normalizer (P : Set Y)) = 21 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hP := card_sylow_seven hcard P
  have hindex : (P : Subgroup Y).index = 864 := by
    have := (P : Subgroup Y).card_mul_index
    rw [hP, hcard] at this
    omega
  have hdvd : Nat.card (Sylow 7 Y) ∣ 864 := hindex ▸ P.card_dvd_index
  have hmod : Nat.card (Sylow 7 Y) % 7 = 1 := card_sylow_modEq_one (p := 7) (G := Y)
  have hidxN : (Subgroup.normalizer (P : Set Y)).index = Nat.card (Sylow 7 Y) :=
    (Sylow.card_eq_index_normalizer P).symm
  have hNcard : Nat.card (Subgroup.normalizer (P : Set Y)) *
      (Subgroup.normalizer (P : Set Y)).index = 6048 := by
    have := (Subgroup.normalizer (P : Set Y)).card_mul_index
    rwa [hcard] at this
  rcases sylow_seven_count_cases hdvd hmod with h1 | h8 | h36 | h288
  · exfalso
    have hsub : Subsingleton (Sylow 7 Y) := (Nat.card_eq_one_iff_unique.mp h1).1
    have hnormal := Sylow.normal_of_subsingleton P
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup Y) with hb | ht
    · rw [hb, Subgroup.card_bot] at hP
      omega
    · rw [ht, Subgroup.card_top, hcard] at hP
      omega
  · exfalso
    have hne : Subgroup.normalizer (P : Set Y) ≠ ⊤ := by
      intro h
      rw [h, Subgroup.index_top] at hidxN
      omega
    have hd := card_dvd_factorial_index hne
    rw [hcard, hidxN, h8] at hd
    have := nine_le_of_dvd_factorial hd
    omega
  · exfalso
    have hN168 : Nat.card (Subgroup.normalizer (P : Set Y)) = 168 := by
      rw [hidxN, h36] at hNcard
      omega
    obtain ⟨u, hu, hcomm⟩ := exists_involution_centralizing (P : Subgroup Y) hP hN168
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P : Subgroup Y)) 7 (by rw [hP])
    exact hnc u b.1 hu (by rw [Subgroup.orderOf_coe]; exact hb) (hcomm b.1 b.2)
  · rw [hidxN, h288] at hNcard
    omega

end CFSG.Quasithin.H13.U3.GC137.SQ
