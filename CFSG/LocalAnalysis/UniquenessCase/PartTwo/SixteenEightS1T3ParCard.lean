module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

private theorem s16t3_eq_of_dvd_two_pow_mul_three_pow {n x a : ℕ}
    (hn : n ∣ 2 ^ x * 3 ^ a) :
    n = 2 ^ (n.factorization 2) * 3 ^ (n.factorization 3) := by
  have hpos : 0 < 2 ^ x * 3 ^ a := by positivity
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hpos.ne' (zero_dvd_iff.mp hn)
  have hsupp : n.factorization.support ⊆ {2, 3} := by
    intro q hq
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hq
    obtain ⟨hqprime, hqdvd, -⟩ := hq
    rcases (Nat.Prime.dvd_mul hqprime).1 (hqdvd.trans hn) with h | h
    · exact Finset.mem_insert.2 (Or.inl ((Nat.prime_dvd_prime_iff_eq hqprime
        Nat.prime_two).1 (hqprime.dvd_of_dvd_pow h)))
    · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2
        ((Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_three).1 (hqprime.dvd_of_dvd_pow h))))
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
  rw [Finsupp.prod_of_support_subset _ hsupp _ fun _ _ => pow_zero _,
    Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3)]

theorem s16t3_pow_three_of_isPGroup_ker {P H : Type*} [Group P] [Group H] (β : P →* H)
    (hker : IsPGroup 2 β.ker) (hH : ∀ h : H, ∀ k : ℕ, h ^ 3 ^ k = 1 → h ^ 3 = 1) :
    ∀ p : P, ∀ k : ℕ, p ^ 3 ^ k = 1 → p ^ 3 = 1 := by
  intro p k hp
  have hβ : β (p ^ 3) = 1 := by
    rw [map_pow]
    exact hH (β p) k (by rw [← map_pow, hp, map_one])
  have hmem : p ^ 3 ∈ β.ker := MonoidHom.mem_ker.2 hβ
  obtain ⟨j, hj⟩ := hker ⟨p ^ 3, hmem⟩
  have h2 : orderOf (p ^ 3) ∣ 2 ^ j := by
    rw [orderOf_dvd_iff_pow_eq_one]
    simpa using hj
  have h3 : orderOf (p ^ 3) ∣ 3 ^ k := by
    refine (orderOf_dvd_of_pow_eq_one ?_).trans (orderOf_dvd_of_pow_eq_one hp)
    rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hcop : Nat.Coprime (3 ^ k) (2 ^ j) :=
    Nat.Coprime.pow k j ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num))
  have hone : orderOf (p ^ 3) = 1 :=
    Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h3 h2)
  exact orderOf_eq_one_iff.mp hone

theorem s16t3_card_of_surjective_isPGroup_ker {E H : Type*} [Group E] [Finite E] [Group H]
    {G P Y : Subgroup E} {x a : ℕ} (hPG : P ≤ G) (hY : CFSG.ABGLocalTools.IsSylowOf 2 Y G)
    (hYP : Y ≤ P) (β : ↥P →* H) (hβ : Function.Surjective β) (hker : IsPGroup 2 β.ker)
    (hH : Nat.card H = 2 ^ x * 3 ^ a) :
    Nat.card ↥P = 3 ^ a * 2 ^ (Nat.card ↥G).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP0 : Nat.card ↥P ≠ 0 := Nat.card_pos.ne'
  have hG0 : Nat.card ↥G ≠ 0 := Nat.card_pos.ne'
  obtain ⟨u, hu⟩ := hker.exists_card_eq
  have hcard : Nat.card ↥P = 2 ^ (u + x) * 3 ^ a := by
    rw [← Subgroup.card_ker_mul_card_of_surjective hβ, hu, hH, pow_add]
    ring
  have hle2 : (Nat.card ↥P).factorization 2 ≤ (Nat.card ↥G).factorization 2 := by
    have h : 2 ^ (Nat.card ↥P).factorization 2 ∣ Nat.card ↥G :=
      ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hP0).mpr le_rfl).trans
        (Subgroup.card_dvd_of_le hPG)
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hG0).mp h
  have hge2 : (Nat.card ↥G).factorization 2 ≤ (Nat.card ↥P).factorization 2 := by
    have hYcard : Nat.card ↥Y = 2 ^ (Nat.card ↥G).factorization 2 := hY.card_eq
    have h : 2 ^ (Nat.card ↥G).factorization 2 ∣ Nat.card ↥P :=
      hYcard ▸ Subgroup.card_dvd_of_le hYP
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hP0).mp h
  have hfac2 : (Nat.card ↥P).factorization 2 = (Nat.card ↥G).factorization 2 :=
    le_antisymm hle2 hge2
  have huv : u + x = (Nat.card ↥G).factorization 2 := by
    have hfac2P : (Nat.card ↥P).factorization 2 = u + x := by
      have h3 : (3 ^ a).factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (fun h => absurd
          (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h) (by norm_num))
      rw [hcard, Nat.factorization_mul (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (by norm_num)), Finsupp.add_apply,
        Nat.factorization_pow_self Nat.prime_two, h3, add_zero]
    rw [← hfac2P, hfac2]
  rw [hcard, huv, mul_comm]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
