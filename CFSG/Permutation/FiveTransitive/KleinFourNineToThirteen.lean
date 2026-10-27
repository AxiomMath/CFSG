module

public import CFSG.Permutation.FiveTransitive.KleinFourFreshOrbit
public import CFSG.Permutation.FiveTransitive.DisjointFinEmbeddingAppend
public import Mathlib.Data.Set.Card

public section

namespace CFSG

namespace FiveTransitive.KleinFourNineToThirteen

open MulAction

theorem exists_extension
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (hsize : 10 ≤ Nat.card X) (e : Fin 9 ↪ X)
    (a c : G) (ha : a * a = 1) (hc : c * c = 1) (hac : a * c = c * a)
    (hfixa : fixedBy X a = {e 0,e 1,e 2,e 3,e 4})
    (hfixc : fixedBy X c = {e 0,e 1,e 2,e 5,e 6})
    (hfixac : fixedBy X (a * c) = {e 0,e 1,e 2,e 7,e 8}) :
    ∃ E : Fin 13 ↪ X,
      (∀ i : Fin 9, E (Fin.castLE (by decide) i) = e i) ∧
      a • E 9 = E 10 ∧ a • E 10 = E 9 ∧ a • E 11 = E 12 ∧ a • E 12 = E 11 ∧
      c • E 9 = E 11 ∧ c • E 11 = E 9 ∧ c • E 10 = E 12 ∧ c • E 12 = E 10 := by
  have hs : Set.range e = fixedBy X a ∪ fixedBy X c ∪ fixedBy X (a * c) := by
    rw [hfixa,hfixc,hfixac]
    ext z
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
      intro hz
      rcases hz with ((hz | hz | hz | hz | hz) | (hz | hz | hz | hz | hz)) |
        (hz | hz | hz | hz | hz)
      all_goals subst z
      all_goals exact Set.mem_range_self _
  have hex : ∃ x : X, x ∉ Set.range e := by
    by_contra! h
    have hu : Set.range e = Set.univ := Set.eq_univ_of_forall h
    have hn := Set.ncard_range_of_injective e.injective
    rw [hu,Set.ncard_univ,Nat.card_fin] at hn
    omega
  obtain ⟨x,hx⟩ := hex
  obtain ⟨f,hf,ha0,ha1,ha2,ha3,hc0,hc2,hc1,hc3⟩ :=
    KleinFourFreshOrbit.orbit_embedding a c ha hc hac (Set.range e) hs x hx
  obtain ⟨E,hE,hF⟩ := DisjointFinEmbeddingAppend.exists_append e f hf
  have h9 : E 9 = f 0 := hF 0
  have h10 : E 10 = f 1 := hF 1
  have h11 : E 11 = f 2 := hF 2
  have h12 : E 12 = f 3 := hF 3
  refine ⟨E,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact hE
  · simpa only [h9,h10] using ha0
  · simpa only [h10,h9] using ha1
  · simpa only [h11,h12] using ha2
  · simpa only [h12,h11] using ha3
  · simpa only [h9,h11] using hc0
  · simpa only [h11,h9] using hc2
  · simpa only [h10,h12] using hc1
  · simpa only [h12,h10] using hc3

end FiveTransitive.KleinFourNineToThirteen

end CFSG
