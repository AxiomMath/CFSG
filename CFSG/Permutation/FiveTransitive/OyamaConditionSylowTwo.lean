module

public import CFSG.Permutation.FiveTransitive.OyamaWholeFixerFixed
public import CFSG.Permutation.FiveTransitive.OyamaSixOrderTwo
public import CFSG.Permutation.FiveTransitive.OyamaConditionAlternatingImage

public section

namespace CFSG

namespace FiveTransitive.OyamaConditionSylowTwo

open MulAction

theorem card_eq_two
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond : OyamaConditionStar.Condition G X) (b : Fin 4 ↪ X)
    (S : Sylow 2 (stabilizer G b)) : Nat.card S = 2 := by
  let H := stabilizer G b
  let A := (S : Subgroup H).map H.subtype
  let e : S ≃* A := (S : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  obtain ⟨hne,_,_,hsemi⟩ := hcond.2.2 b S
  let _ : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hne
  let _ : Nontrivial S := Function.Injective.nontrivial e.symm.injective
  have hfixed : fixedPoints A X = fixedPoints S X :=
    OyamaSixElementary.fixedPoints_image G X H S
  have hfreeA : ∀ (q : A) (x : X), x ∉ fixedPoints A X → q • x = x → q = 1 := by
    intro q x hx hqx
    by_contra hq
    exact hsemi q.val q.property (fun h => hq (Subtype.ext h)) x hx hqx
  have hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1 := by
    intro q x hx hqx
    apply e.injective
    rw [map_one]
    exact hfreeA (e q) x (by rwa [hfixed]) hqx
  have hc : (fixedPoints S X).ncard = 6 := by
    rw [←hfixed,←Nat.card_coe_set_eq]
    exact (hcond.2.1 b S).1
  have hs : (Set.range b).ncard = 4 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective b.injective
  have h4 := OyamaConditionFourTransitive.four_transitive hcond
  have hn : 10 ≤ Fintype.card X := by simpa only [Nat.card_eq_fintype_card] using hcond.1
  have himage := OyamaConditionAlternatingImage.image_eq_alternating hcond b S
  have hH := OyamaWholeFixerFixed.fixedPoints_eq hcond (Set.range b) hs
  have main := OyamaSixOrderTwo.card_eq_two G X hn h4 (Set.range b) hs
  rw [EvenSixTupleLocal.fixing_range] at main hH
  exact main S hH hfree hc himage

end FiveTransitive.OyamaConditionSylowTwo

end CFSG
