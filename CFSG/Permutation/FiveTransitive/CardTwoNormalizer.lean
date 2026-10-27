module

public import CFSG.Permutation.FiveTransitive.NormalizerTwoElementInvolution

public section

namespace CFSG

namespace FiveTransitive.CardTwoNormalizer

theorem normalizer_eq_centralizer
    {G : Type*} [Group G] (Q : Subgroup G) (hQ : Nat.card Q = 2)
    (q : Q) (hq : q ≠ 1) :
    Subgroup.normalizer (Q : Set G) = Subgroup.centralizer ({(q : G)} : Set G) := by
  apply le_antisymm
  · intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (NormalizerTwoElementInvolution.central_of_card_two Q hQ ⟨g, hg⟩ q).symm
  · intro g hg
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases Research.OddIndexTwoConjugacy.eq_one_or_eq_of_natCard_eq_two hQ q hq
      (⟨x, hx⟩ : Q) with h | h
    · have he : x = 1 := congrArg Subtype.val h
      simp only [he, one_mul, mul_one]
    · have he : x = (q : G) := congrArg Subtype.val h
      rw [he]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hg).symm

end FiveTransitive.CardTwoNormalizer

end CFSG
