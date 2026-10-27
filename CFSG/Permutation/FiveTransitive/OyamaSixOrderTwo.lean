module

public import CFSG.Permutation.FiveTransitive.OyamaSixOrderAlternatives
public import CFSG.Permutation.FiveTransitive.OyamaSmallSylowNotFour
public import CFSG.Permutation.FiveTransitive.OyamaSixteenContradiction

public section

namespace CFSG

namespace FiveTransitive.OyamaSixOrderTwo

open MulAction

theorem card_eq_two
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hX : 10 ≤ Fintype.card X) (h4 : IsMultiplyPretransitive G X 4)
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup G s)) [Nontrivial S]
    (hH : fixedPoints (fixingSubgroup G s) X = s)
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hcard : (fixedPoints S X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X)) :
    Nat.card S = 2 := by
  rcases OyamaSixOrderAlternatives.card_eq_two_four_or_sixteen
    G X hX h4 s hs S hfree hcard himage with htwo | hfour | hsixteen
  · exact htwo
  · exact (OyamaSmallSylowNotFour.card_ne_four G X hX h4 s hs S hfree hcard himage hfour).elim
  · obtain ⟨b,hb⟩ := BaseSylowConjugacy.exists_embedding_range X 4 s hs
    subst s
    exact (OyamaSixteenContradiction.contradiction G X h4 b S hH hfree hcard himage hsixteen).elim

end FiveTransitive.OyamaSixOrderTwo

end CFSG
