module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartTwo.Sec21.Item2113Res2ProofKappa
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

namespace Item21Res7Proof

open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open Subgroup

theorem mem_inner_of_not_three_dvd {S : Type*} [Group S] (hS : ¬ 3 ∣ Nat.card (Outer S))
    {τ : MulAut S} {k : ℕ} (hτ : τ ^ (3 ^ k) = 1) : τ ∈ inner S := by
  set o : Outer S := QuotientGroup.mk τ with ho
  have hok : o ^ (3 ^ k) = 1 := by rw [ho, ← QuotientGroup.mk_pow, hτ, QuotientGroup.mk_one]
  have hdvdk : orderOf o ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hok
  have hdvdO : orderOf o ∣ Nat.card (Outer S) := orderOf_dvd_natCard o
  have hord : orderOf o = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvdk
    rcases j with _ | j
    · simpa using hj
    · exact absurd ((dvd_pow_self 3 (Nat.succ_ne_zero j)).trans (hj ▸ hdvdO)) hS
  have ho1 : o = 1 := orderOf_eq_one_iff.mp hord
  rw [ho, QuotientGroup.eq_one_iff] at ho1
  exact ho1

variable {G : Type} [Group G] [Finite G]

end Item21Res7Proof

end CFSG.RankThree.PartTwo.Sec21
