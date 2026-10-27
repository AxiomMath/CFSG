module
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_18_a

namespace CFSG
end CFSG
open CFSG
/-! # Theorem 4.18(b) from BG Section 4 -/

universe u

section Main

open scoped FixedPoints

private theorem CFSG.isPGroup_of_unique_prime_dvd_natCard
    (G : Type*) [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (huniq : ∀ q : ℕ, q.Prime → q ∣ Nat.card G → q = p) :
    IsPGroup p G := by
  have hcard : Nat.card G = p ^ (Nat.card G).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (by
      intro q hq hq_dvd
      exact huniq q hq hq_dvd)
  exact IsPGroup.of_card (p := p) (G := G) hcard

public theorem CFSG.theorem_4_18_b {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hsolv : IsSolvable G) (hodd : Odd (Nat.card G)) (hp_mem : p ∣ Nat.card G)
    (hrank : primeRank p G ≤ 2)
    (hp_small : p = 3 ∨ IsSmallestPrimeDivisor p (Nat.card G)) :
    HasNormalPComplement p G := by
  have hlargest : IsLargestPrimeDivisor p (Nat.card (G ⧸ pPrimeCore p G)) :=
    theorem_4_18_a (G := G) (p := p) hsolv hodd hp_mem hrank
  have hQp : IsPGroup p (G ⧸ pPrimeCore p G) := by
    refine isPGroup_of_unique_prime_dvd_natCard (G ⧸ pPrimeCore p G) (p := p) ?_
    intro q hq hq_dvd
    have hq_le_p : q ≤ p := hlargest.2.2 q hq hq_dvd
    have hp_le_q : p ≤ q := by
      rcases hp_small with hp3 | hsmall
      · subst hp3
        have hq_dvd_G : q ∣ Nat.card G :=
          hq_dvd.trans (Subgroup.card_quotient_dvd_card (s := pPrimeCore 3 G))
        have hq_ne_two : q ≠ 2 := by
          intro hq_two
          have hodd_q : Odd q := hodd.of_dvd_nat hq_dvd_G
          rw [hq_two] at hodd_q
          exact (by norm_num [Nat.odd_iff] at hodd_q)
        by_cases hq_three : q = 3
        · omega
        · have hfive : 5 ≤ q := Nat.Prime.five_le_of_ne_two_of_ne_three hq hq_ne_two hq_three
          omega
      · exact hsmall.2.2 q hq (hq_dvd.trans (Subgroup.card_quotient_dvd_card (s := pPrimeCore p G)))
    exact le_antisymm hq_le_p hp_le_q
  refine ⟨pPrimeCore p G, inferInstance, pPrimeCore_coprime_card (G := G) (p := p), ?_⟩
  exact hQp

end Main
