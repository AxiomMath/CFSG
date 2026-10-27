module

public import CFSG.CharacterTheory.TwoRankLowerBound.InvolutionRoots
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingConsequences

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem noncentralSylow_two_rank_of_even_involution_product
    {t s : G} (ht : orderOf t = 2) (hs : orderOf s = 2)
    (heven : Even (orderOf (t * s))) : 2 ≤ CFSG.Open.twoRank G := by
  have hts : t ≠ s := by
    intro heq
    rw [heq, ← pow_two, (orderOf_eq_prime_iff.mp hs).1] at heven
    norm_num at heven
  obtain ⟨v, hv, hvpow, htv, _hsv⟩ :=
    central_rotation_of_even_involution_product ht hs heven
  have htvne : t ≠ v := by
    intro heq
    let R := Subgroup.zpowers (t * s)
    have htR : t ∈ R := heq.symm ▸ hvpow
    have hsR : s ∈ R := by
      have hh := R.mul_mem htR (Subgroup.mem_zpowers (t * s))
      have htt : t * t = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht).1
      simpa only [← mul_assoc, htt, one_mul] using hh
    exact hts (commuting_involutions_eq_in_cyclic_subgroup R t s htR hsR ht hs)
  exact two_le_twoRank_of_commuting_involutions G t v ht hv htvne htv

end CFSG.ShultStronglyClosedTI
