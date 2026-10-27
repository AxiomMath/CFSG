module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompPerf
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin

namespace S143

namespace InspW2

section Sylow

variable {Q : Type*} [Group Q] [Finite Q]

theorem sylow_perfect_facts [Nontrivial Q] [Group.IsPerfect Q] (S : Sylow 2 Q) :
    4 ≤ Nat.card S ∧ ¬ IsCyclic S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hncyc : ¬ IsCyclic S := by
    intro hcyc
    refine false_of_perfect_cyclic_sylow_quot (C := ⊥) bot_le S ?_
    have hsurj := MonoidHom.subgroupMap_surjective (QuotientGroup.mk' (⊥ : Subgroup Q))
      (S : Subgroup Q)
    exact isCyclic_of_surjective _ hsurj
  refine ⟨?_, hncyc⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
  by_contra hlt
  have hn2 : n ≤ 1 := by
    by_contra hn2
    apply hlt
    rw [hn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
  · apply hncyc
    have : Subsingleton S := (Nat.card_eq_one_iff_unique.mp (by rw [hn]; simp)).1
    infer_instance
  · apply hncyc
    have : Fact (Nat.Prime (Nat.card S)) := ⟨by rw [hn]; simpa using Nat.prime_two⟩
    exact isCyclic_of_prime_card rfl

end Sylow

theorem sq_eq_one_of_card_four {S : Type*} [Group S] [Finite S] (hc : Nat.card S = 4)
    (hncyc : ¬ IsCyclic S) (s : S) : s * s = 1 := by
  have hdvd : orderOf s ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hc]; exact orderOf_dvd_natCard s
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h2 : s ^ 2 = 1 := by
    interval_cases k
    · rw [pow_zero] at hk'; rw [orderOf_eq_one_iff.mp hk']; simp
    · apply orderOf_dvd_iff_pow_eq_one.mp; rw [hk']; simp
    · exact absurd (isCyclic_of_orderOf_eq_card s (by rw [hk', hc]; norm_num)) hncyc
  rwa [pow_two] at h2

end InspW2

end S143

end CFSG.Quasithin
