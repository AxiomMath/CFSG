module

public import CFSG.Permutation.FiveTransitive.ClassifiedOddSemiregularFive
public import CFSG.Permutation.FiveTransitive.FourTransitiveTwoPart
public import CFSG.Permutation.FiveTransitive.FreeComplementCard

public section

namespace CFSG

namespace FiveTransitive.ClassifiedOddSemiregularFiveOrders

open MulAction TupleSemiregularFour

theorem degree_order_pairs
    (X : Type*) [Fintype X] [DecidableEq X] (P : Subgroup (Equiv.Perm X))
    (h5 : IsMultiplyPretransitive P X 5) (hodd : Odd (Fintype.card X))
    (hlarge : 7 ≤ Fintype.card X)
    (e : Fin 5 ↪ X) (S : Sylow 2 (stabilizer P e))
    (hS : (S : Subgroup (stabilizer P e)) ≠ ⊥)
    (hfix : Nat.card (fixedPoints (image e S) X) = 5)
    (hfree : ∀ q : P, q ∈ image e S → q ≠ 1 →
      ∀ x : X, x ∉ fixedPoints (image e S) X → q • x ≠ x)
    (hclass : Nat.card P = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧ Nat.card P = (Fintype.card X).factorial / 2) ∨
      (Fintype.card X = 12 ∧ Nat.card P = 95040) ∨
      (Fintype.card X = 24 ∧ Nat.card P = 244823040)) :
    (Fintype.card X = 7 ∧ Nat.card P = 5040) ∨
      (Fintype.card X = 9 ∧ Nat.card P = 181440) := by
  have hsmall := ClassifiedOddSemiregularFive.card_le_nine X P h5 hodd e S hfix hfree hclass
  have ho := Nat.odd_iff.mp hodd
  have hdegree : Fintype.card X = 7 ∨ Fintype.card X = 9 := by omega
  have horders : Nat.card P = (Fintype.card X).factorial ∨
      Nat.card P = (Fintype.card X).factorial / 2 := by
    rcases hclass with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h.2
    · omega
    · omega
  have hd := FreeComplementCard.card_dvd_complement (image e S) X
    (fixedPoints (image e S) X) (by
      intro q x hx
      simpa only [mem_fixedPoints.mp hx q] using hx) (by
      intro q x hx hq
      by_contra hne
      exact hfree q q.property (fun h => hne (Subtype.ext h)) x hx hq)
  have himage : Nat.card (image e S) = Nat.card S :=
    Subgroup.card_map_of_injective (stabilizer P e).subtype_injective
  rw [himage, ← Nat.card_coe_set_eq, hfix, show Nat.card X = Fintype.card X from Nat.card_eq_fintype_card] at hd
  have hi := @index_stabilizer_of_transitive P (Fin 5 ↪ X) _ _ e h5
  rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin] at hi
  have hc := (stabilizer P e).index_mul_card
  rcases hdegree with hn | hn
  · rcases horders with hg | hg
    · exact Or.inl ⟨hn, by simpa [hn, Nat.factorial] using hg⟩
    · norm_num [hn, Nat.factorial, Nat.descFactorial_succ] at hi hg
      rw [hi,hg] at hc
      have hh : Nat.card (stabilizer P e) = 1 := by omega
      have hScard : Nat.card S = 1 := FourTransitiveTwoPart.sylow_card_of_two_pow_mul_odd
        0 1 (by simpa using hh) (by decide) S
      have hntr : Nontrivial S := (S : Subgroup (stabilizer P e)).nontrivial_iff_ne_bot.mpr hS
      have htwo := Finite.one_lt_card_iff_nontrivial.mpr hntr
      omega
  · rcases horders with hg | hg
    · norm_num [hn, Nat.factorial, Nat.descFactorial_succ] at hi hg
      rw [hi,hg] at hc
      have hh : Nat.card (stabilizer P e) = 24 := by omega
      have hScard : Nat.card S = 8 := FourTransitiveTwoPart.sylow_card_of_two_pow_mul_odd
        3 3 (by simpa using hh) (by decide) S
      rw [hScard, hn] at hd
      norm_num at hd
    · exact Or.inr ⟨hn, by simpa [hn, Nat.factorial] using hg⟩

end FiveTransitive.ClassifiedOddSemiregularFiveOrders

end CFSG
