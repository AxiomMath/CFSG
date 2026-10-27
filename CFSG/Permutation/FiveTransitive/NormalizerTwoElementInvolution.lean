module

public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerHom
public import CFSG.Permutation.FiveTransitive.OddIndexTwoConjugacy

public section

namespace CFSG

namespace FiveTransitive.NormalizerTwoElementInvolution

open MulAction FixedSetNormalizerHom

theorem central_of_card_two
    {G : Type*} [Group G] (Q : Subgroup G) (hQ : Nat.card Q = 2)
    (n : Subgroup.normalizer (Q : Set G)) (q : Q) :
    (q : G) * (n : G) = (n : G) * q := by
  have heq : Q.normalizerMonoidHom n q = q := by
    by_cases hq : q = 1
    · rw [hq, map_one]
    · rcases Research.OddIndexTwoConjugacy.eq_one_or_eq_of_natCard_eq_two
        hQ q hq (Q.normalizerMonoidHom n q) with h | h
      · exact False.elim (hq ((Q.normalizerMonoidHom n).injective (h.trans (map_one _).symm)))
      · exact h
  have h := congrArg (fun q : Q => (q : G)) heq
  rw [Q.normalizerMonoidHom_apply_apply_coe] at h
  exact ((mul_inv_eq_iff_eq_mul).mp h).symm

end FiveTransitive.NormalizerTwoElementInvolution

end CFSG
