module

public import CFSG.Quasithin.EmptyFaithful.A38c8Defs
public import CFSG.Quasithin.EmptyFaithful.A38c8Out
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal

public section

namespace CFSG.Quasithin.A38c8

open CFSG.Open CFSG.QuasithinUnique

theorem center_eq_bot_of_isSporadic_j4 {X : Type} [Group X]
    (h : IsSporadic .J4 X) : Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := h
  have hs0 : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
    CFSG.Sporadic.J4.fam_j4_simplicity.2.2
  have hs : IsSimpleGroup X := e.isSimpleGroup
  have hc : Nat.card X = 86775571046077562880 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J4.card_J4
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h1 | h1
  · exact h1
  · exfalso
    have : IsMulCommutative X := Subgroup.center_eq_top_iff.1 h1
    have hp := Group.is_simple_iff_prime_card.1 hs
    rw [hc] at hp
    norm_num at hp

theorem odd_card_outer_of_isSporadic_j4
    {X : Type} [Group X]
    (h : IsSporadic .J4 X) :
    Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact CFSG.QuasithinUnique.Setup.X1.j4OuterOdd

theorem inner_of_j4
    (hJ : J4L4Inner) {Y : Type}
    [Group Y] [Finite Y] {N T B : Subgroup Y} (hN : N.Normal) (hM : IsSporadic .J4 ↥N)
    (hT : IsSylowTwoOf T ⊤) (hBN : B ≤ N) (hB : B ∈ lFamily T)
    (hTB : T ≤ Subgroup.normalizer (B : Set Y)) (h4 : IsPSL 4 2 1 (ModO2 B)) :
    ∀ t ∈ T, InnerOnModO2 B t := by
  intro t ht
  obtain ⟨x, hxTN, hconj⟩ := exists_mem_inf_inner_of_odd_outer hN hT
    (center_eq_bot_of_isSporadic_j4 hM) (odd_card_outer_of_isSporadic_j4 hM) t ht
  obtain ⟨b, hb, hbx⟩ := hJ Y N T B hN hM hT hBN hB hTB h4 x hxTN
  refine ⟨b, hb, fun y hy => ?_⟩
  rw [hconj y (hBN hy)]
  exact hbx y hy

end CFSG.Quasithin.A38c8
