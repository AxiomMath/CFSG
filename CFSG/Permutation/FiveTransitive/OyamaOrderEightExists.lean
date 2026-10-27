module

public import CFSG.Permutation.FiveTransitive.OyamaOrderFourWitness
public import CFSG.Permutation.FiveTransitive.SixteenOrderFourCentralizer

public section

namespace CFSG

namespace FiveTransitive.OyamaOrderEightExists

open MulAction

theorem exists_order_eight
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hX : 10 ≤ Fintype.card X)
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s)) [Nontrivial S]
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hcard : (fixedPoints S X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (hS : Nat.card S = 16) : ∃ a : G, orderOf a = 8 := by
  let H := fixingSubgroup G s
  let Q : Subgroup G := (S : Subgroup H).map H.subtype
  obtain ⟨a, haN, ha, _, haFix, haZero, haSqTwo⟩ := OyamaOrderFourWitness.exists_order_four_normalizer
    G X hX h4 s hs S hfree hcard himage hS
  let e : S ≃* Q := (S : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  have he : ∀ (q : S) (x : X), (Equiv.refl X) (q • x) = e q • (Equiv.refl X) x := by
    intro q x
    rfl
  have hfreeQ := EquivariantSemiregular.free_of_equivariant S Q X X e (Equiv.refl X) he hfree
  obtain ⟨hsq, hcomm⟩ := OyamaSixElementary.square_eq_one_and_commute G X h4 s hs S hfree hcard himage
  obtain ⟨hQ2, hQcomm⟩ := EquivariantSemiregular.square_and_commute_of_equiv S Q e hsq hcomm
  have hQcard : Nat.card Q = 16 := (Nat.card_congr e.toEquiv).symm.trans hS
  have haSq : orderOf (a ^ 2) = 2 := by rw [orderOf_pow, ha]; norm_num
  have haSqSix := OyamaSixOrderSixteen.involution_fixed_six G X hX h4 s hs S hfree hcard himage hS
    (a ^ 2) haSq
  have ha4 : a ^ 4 = 1 := ha ▸ pow_orderOf_eq_one a
  obtain ⟨q, hq⟩ := SixteenOrderFourCentralizer.exists_order_eight G X Q hQcomm hQ2 hQcard hfreeQ
    a haN ha4 haFix haZero haSqSix haSqTwo
  exact ⟨(q : G) * a, hq⟩

end FiveTransitive.OyamaOrderEightExists

end CFSG
