module

public import CFSG.RankThree.PartTwo.Sec21.LitScopeProofGL83
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.StrongThreeSolv

public section

namespace CFSG.RankThree.PartTwo.Sec21

open scoped commutatorElement

theorem gl83StronglyEmbeddedNoSimpleThree_of_kFactStrongThreeSolv
    (h : CFSG.AGLEmbeddingD2.McLaughlin.KFactStrongThreeSolv) :
    GL83StronglyEmbeddedNoSimpleThree := by
  intro X _ _ hK M hM hrank H hHM hH
  have hKo : CFSG.Open.IsKGroup X := CFSG.KCore.KGroupAllSimple.kGroupNonab hK
  by_cases hab : ∀ a b : H, a * b = b * a
  ·
    letI : CommGroup H := { (inferInstance : Group H) with mul_comm := hab }
    have hp : (Nat.card H).Prime := IsSimpleGroup.prime_card (α := H)
    by_cases h3 : 3 ∣ Nat.card H
    · left
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3).symm
    · right
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  ·
    push Not at hab
    have hperf : ⁅H, H⁆ = H := by
      rw [← Subgroup.isPerfect_iff, Group.isPerfect_def]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator H) with h0 | h0
      · exfalso
        obtain ⟨a, b, hab⟩ := hab
        have hc : ⁅a, b⁆ ∈ commutator H := by
          rw [commutator_def]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
        exact hab hc
      · exact h0
    right
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (h X hKo M hM hrank H hHM hperf)

end CFSG.RankThree.PartTwo.Sec21
