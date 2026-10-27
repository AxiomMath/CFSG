module

public import CFSG.Permutation.FiveTransitive.Degree72ElevenCentralizingSpread
public import CFSG.Permutation.FiveTransitive.AbelianOrbitEvaluation

public section

namespace CFSG

namespace FiveTransitive.Degree72ElevenCentralizingBound
open MulAction

theorem card_eq_eleven
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hcard : Fintype.card X = 72) (Q : Subgroup G) [IsMulCommutative Q]
    (hcommon : Nat.card (fixedPoints Q X) = 6)
    (horbit : ∀ x : X, x ∉ fixedPoints Q X → Nat.card (orbit Q x) = 11)
    (hfixed : ∀ a : G, a ≠ 1 → Nat.card (fixedBy X a) ≤ 36)
    (g : Subgroup.normalizer (Q : Set G)) (hg : orderOf g = 5)
    (hcomm : ∀ q : Q, g.val * q.val = q.val * g.val) : Nat.card Q = 11 := by
  classical
  have hgval : g.val ≠ 1 := by
    intro he
    have hg1 : g = 1 := Subtype.ext he
    rw [hg1,orderOf_one] at hg
    omega
  have hgf := hfixed g.val hgval
  have hxexists : ∃ x : X, x ∉ fixedPoints Q X ∧ g.val • x ≠ x := by
    by_contra hn
    push Not at hn
    have hcover : fixedPoints Q X ∪ fixedBy X g.val = Set.univ := by
      apply Set.eq_univ_iff_forall.mpr
      intro x
      by_cases hx : x ∈ fixedPoints Q X
      · exact Or.inl hx
      · exact Or.inr (hn x hx)
    have hb := Set.ncard_union_le (fixedPoints Q X) (fixedBy X g.val)
    rw [hcover,Set.ncard_univ,Nat.card_eq_fintype_card,hcard,
      ← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,hcommon] at hb
    omega
  obtain ⟨x,hxF,hxg⟩ := hxexists
  have hOx := horbit x hxF
  obtain ⟨D,hD,_,hRD⟩ := Degree72ElevenCentralizingSpread.exists_fixed_spread Q g hg hcomm x hxg hOx
  have hfree (q : Q) (hq : q • x = x) : q = 1 := by
    by_contra hne
    have hqne : q.val ≠ 1 := fun he => hne (Subtype.ext he)
    have hb := hfixed q.val hqne
    have hsub : D ⊆ fixedBy X q.val := by
      intro y hy
      exact hRD (⟨q,hq⟩ : stabilizer Q x) y hy
    have hle := Set.ncard_le_ncard hsub
    rw [hD,← Nat.card_coe_set_eq] at hle
    omega
  have hle := AbelianOrbitEvaluation.card_le_orbit (G := Q) x hfree
  rw [hOx] at hle
  have hd := (stabilizer Q x).index_dvd_card
  rw [index_stabilizer,← Nat.card_coe_set_eq,hOx] at hd
  exact Nat.le_antisymm hle (Nat.le_of_dvd Nat.card_pos hd)

end FiveTransitive.Degree72ElevenCentralizingBound

end CFSG
