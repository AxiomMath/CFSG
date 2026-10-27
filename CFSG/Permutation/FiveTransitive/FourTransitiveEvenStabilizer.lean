module

public import CFSG.Permutation.FiveTransitive.HighDegreeHallReduction
import CFSG.Permutation.FiveTransitive.BaseSylowConjugacy

public section

namespace CFSG

namespace FiveTransitive.FourTransitiveEvenStabilizer

open MulAction

theorem even_card_fixingSubgroup
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hcard : 27 ≤ Fintype.card X)
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (s : Set X) (hs : s.ncard = 4) :
    Even (Nat.card (fixingSubgroup G s)) := by
  classical
  let _ := Fintype.ofFinite s
  have hscard : Fintype.card s = 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hs]
  let es : Fin 4 ≃ s := (Fintype.equivFinOfCardEq hscard).symm
  let e : Fin 4 ↪ X := es.toEmbedding.trans (Function.Embedding.subtype _)
  have hrange : Set.range e = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (es i).property
    · intro hx
      obtain ⟨i, hi⟩ := es.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  apply Nat.not_odd_iff_even.mp
  have h := Research.HighDegreeHallReduction.fourTransitiveOddStabilizerImpossibleAtLeastTwentySeven
    G X (by simpa only [Nat.card_eq_fintype_card] using hcard) h4 e
  rw [← FiveTransitive.BaseSylowConjugacy.fixing_range_eq_stabilizer G X e,
    hrange] at h
  exact h

theorem exists_order_two_fixing
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hcard : 27 ≤ Fintype.card X)
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (s : Set X) (hs : s.ncard = 4) :
    ∃ g : G, orderOf g = 2 ∧ ∀ x ∈ s, g • x = x := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card (fixingSubgroup G s) := by
    obtain ⟨k, hk⟩ := even_card_fixingSubgroup G X hcard h4 s hs
    exact ⟨k, by omega⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  exact ⟨g, (Subgroup.orderOf_coe g).trans hg, (mem_fixingSubgroup_iff G).mp g.property⟩

end FiveTransitive.FourTransitiveEvenStabilizer

end CFSG
