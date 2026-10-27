module

public import CFSG.Quasithin.Vol2.Ch11SecO6E
public import CFSG.Quasithin.Vol2.Ch11SecGFacts2
public import CFSG.Quasithin.Vol2.Ch11SecAKE12
public import CFSG.Quasithin.Vol2.Ch11SecAKE14
public import CFSG.RankThree.PartOne.K128.TorusShape

public section

namespace CFSG.Quasithin.Vol2.Ch11.O6

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter

theorem card_psl2_prime {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsPSL 2 p 1 X) : Nat.card X = p * (p ^ 2 - 1) / 2 := by
  have hc := H13.NotLie.card_psl2 h
  have hg : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
    rw [pow_one]
    exact Nat.gcd_eq_left (Nat.Prime.even_sub_one hp hp2).two_dvd
  rwa [hg, pow_one] at hc

theorem card_psl2_lt {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) :
    p * (p ^ 2 - 1) / 2 < q * (q ^ 2 - 1) / 2 := by
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hpq' : (p : ℤ) + 1 ≤ q := by exact_mod_cast hpq
  have hp' : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have key : p * (p ^ 2 - 1) + 2 ≤ q * (q ^ 2 - 1) := by
    zify [h1, h2]
    have hqp : (1 : ℤ) ≤ q - p := by linarith
    have hsq : (11 : ℤ) ≤ (q : ℤ) ^ 2 + q * p + p ^ 2 - 1 := by nlinarith
    have hm : (1 : ℤ) * 11 ≤ (q - p) * ((q : ℤ) ^ 2 + q * p + p ^ 2 - 1) :=
      mul_le_mul hqp hsq (by norm_num) (by linarith)
    nlinarith [hm]
  calc p * (p ^ 2 - 1) / 2 < (p * (p ^ 2 - 1) + 2) / 2 := by omega
    _ ≤ q * (q ^ 2 - 1) / 2 := Nat.div_le_div_right key

theorem eq_of_card_psl2 {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h : p * (p ^ 2 - 1) / 2 = q * (q ^ 2 - 1) / 2) : p = q := by
  rcases lt_trichotomy p q with hlt | heq | hgt
  · exact absurd h (card_psl2_lt hp hlt).ne
  · exact heq
  · exact absurd h (card_psl2_lt hq hgt).ne'

theorem dvd_card_psl2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p ∣ p * (p ^ 2 - 1) / 2 := by
  have h2 : 2 ∣ p ^ 2 - 1 := (Nat.Odd.sub_odd ((hp.odd_of_ne_two hp2).pow) odd_one).two_dvd
  rw [Nat.mul_div_assoc p h2]
  exact dvd_mul_right p _

theorem pRank_three_le_of_isPSL2 {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (h7 : 7 ≤ p) (hX : IsPSL 2 p 1 X) : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hX
  let e : X ≃* PSL2 K := e₀.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hcyc := CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card K hK
    (by rw [hK, pow_one]; exact h7) 3 (by norm_num)
    (by rw [hK, pow_one]; exact (Nat.coprime_primes (by norm_num) hp).mpr (by omega))
  have h1 := CFSG.RankThree.PartOne.K128.pRank_le_one_of_cyclic_sylow (p := 3) hcyc
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h1
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact h1

theorem card_psl2_ne {p N : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (h : p * (p ^ 2 - 1) / 2 = N)
    (hN : N = 7800 ∨ N = 372000 ∨ N = 175560) : False := by
  have hpN : p ∣ N := h ▸ dvd_card_psl2 hp (by omega)
  rcases hN with rfl | rfl | rfl
  · have hm : p ∈ Nat.primeFactors 7800 := Nat.mem_primeFactors.2 ⟨hp, hpN, by norm_num⟩
    have hpf : Nat.primeFactors 7800 = {2, 3, 5, 13} := by norm_num [Nat.primeFactors]
    rw [hpf] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> omega
  · have hm : p ∈ Nat.primeFactors 372000 := Nat.mem_primeFactors.2 ⟨hp, hpN, by norm_num⟩
    have hpf : Nat.primeFactors 372000 = {2, 3, 5, 31} := by norm_num [Nat.primeFactors]
    rw [hpf] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> omega
  · have hm : p ∈ Nat.primeFactors 175560 := Nat.mem_primeFactors.2 ⟨hp, hpN, by norm_num⟩
    have hpf : Nat.primeFactors 175560 = {2, 3, 5, 7, 11, 19} := by norm_num [Nat.primeFactors]
    rw [hpf] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

end CFSG.Quasithin.Vol2.Ch11.O6

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank


theorem factL2pListMod5_holds : FactL2pListMod5 := by
  intro X _ _ p hp h11 hX hl
  have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p 1 hX).2
  have hcard := O6.card_psl2_prime hp (by omega) hX
  have hr3 := O6.pRank_three_le_of_isPSL2 hp (by omega) hX
  have hord : ∀ N, Nat.card X = N → N = 7800 ∨ N = 372000 ∨ N = 175560 → False :=
    fun N hN h => O6.card_psl2_ne hp h11 (hcard.symm.trans hN) h
  rcases hl with h2 | h3
  · have := (SecA.factList2Table_holds X 2 le_rfl h2).2.2 3 Nat.prime_three (by norm_num)
    omega
  obtain ⟨h1, -⟩ := SecA.factList3Table_holds
  have k1 := fun h => (h1 X h).2.2.1
  rcases h3 with h | h | ⟨q, hq, hq5, -, h⟩ | h | ⟨s, h | h⟩ | h | h | h | h | h | h | h | h | h | h
  · have := k1 (Or.inl h)
    omega
  · have := k1 (by simp only [h, true_or, or_true])
    omega
  · have hq11 : 11 ≤ q := by
      by_contra hlt
      have hq2 := hq.two_le
      have hlt' : q < 11 := by omega
      interval_cases q <;> first | omega | exact absurd hq (by norm_num)
    have hcq := O6.card_psl2_prime hq (by omega) h
    have hpq : p = q := O6.eq_of_card_psl2 (by omega) (by omega) (hcard.symm.trans hcq)
    rw [hpq]
    exact hq5
  · exact (hord 7800 (by rw [H13.NotLie.card_psl2 h]; norm_num) (Or.inl rfl)).elim
  · cases s
    · have := k1 (by simp only [h, true_or, or_true])
      omega
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
      let e₁ : X ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
        e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
      refine (hord 372000 ?_ (Or.inr (Or.inl rfl))).elim
      rw [Nat.card_congr e₁.toEquiv,
        CFSG.OrderReductions.LinearOrders.card_specialLinear K 3 (by norm_num), hK]
      decide
  · cases s
    · have := k1 (by simp only [h, or_true])
      omega
    · exact (hord 372000 (H13.NotLie.card_psl35 h) (Or.inr (Or.inl rfl))).elim
  · have := k1 (by simp only [h, true_or, or_true])
    omega
  · have := k1 (by simp only [h, true_or, or_true])
    omega
  · have := k1 (by simp only [h, true_or, or_true])
    omega
  · obtain ⟨e⟩ := h
    let e' : X ≃* ↥CFSG.Sporadic.J1.J := e.trans CFSG.Sporadic.J1.nativeEquiv
    exact (hord 175560 ((Nat.card_congr e'.toEquiv).trans CFSG.Sporadic.J1.card_J)
      (Or.inr (Or.inr rfl))).elim
  · have := k1 (by simp only [h, true_or, or_true])
    omega
  · have := k1 (by simp only [h, true_or, or_true])
    omega
  · have := k1 (by simp only [h, true_or, or_true])
    omega
  · have := k1 (by simp only [h, true_or, or_true])
    omega
  · obtain ⟨-, -, ⟨e⟩, -⟩ := h
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact (O6.false_of_simple (p := 5) (by norm_num) (φ := e.toMonoidHom.comp (QuotientGroup.mk' _))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))).elim
  · obtain ⟨q, hq, -, hq8, -, -, -, ψ, hψ, -, -⟩ := h
    have : Fact q.Prime := ⟨hq⟩
    exact (O6.false_of_simple (p := q) (by omega) hψ).elim

end CFSG.Quasithin.Vol2.Ch11.SecG
