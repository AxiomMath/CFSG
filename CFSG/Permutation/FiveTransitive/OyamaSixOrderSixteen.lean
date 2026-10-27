module

public import CFSG.Permutation.FiveTransitive.OyamaSixNormalizerRepresentative
public import CFSG.Permutation.FiveTransitive.OyamaSixOrderUpper
public import CFSG.Permutation.FiveTransitive.SixteenNormalizerInvolutions

public section

namespace CFSG

namespace FiveTransitive.OyamaSixOrderSixteen

open MulAction FixedSetNormalizerHom

theorem involution_fixed_six
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
    (hS : Nat.card S = 16) (a : G) (ha : orderOf a = 2) :
    (fixedBy X a).ncard = 6 := by
  classical
  let H := fixingSubgroup G s
  let Q : Subgroup G := (S : Subgroup H).map H.subtype
  obtain ⟨hsq, hcomm⟩ := OyamaSixElementary.square_eq_one_and_commute G X h4 s hs S hfree hcard himage
  let e : S ≃* Q := (S : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  obtain ⟨_, hQcomm⟩ := EquivariantSemiregular.square_and_commute_of_equiv S Q e hsq hcomm
  have hcardQ : (fixedPoints Q X).ncard = 6 := by
    rw [OyamaSixElementary.fixedPoints_image]
    exact hcard
  have heven := OyamaSixOrderUpper.even_of_alternating_image G X Q himage
  obtain ⟨b, hb⟩ := exists_ne (1 : S)
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by simpa only [pow_two] using hsq b) hb
  let bG : G := ((b : H) : G)
  have hbG2 : orderOf bG = 2 :=
    (Subgroup.orderOf_coe (b : H)).trans ((Subgroup.orderOf_coe b).trans hb2)
  have hbfix : (fixedBy X bG).ncard = 6 := by
    change (fixedBy X b).ncard = 6
    rw [SemiregularSylowFixedSet.fixedBy_eq_fixedPoints S X hfree b hb, hcard]
  have hbmoved : 4 ≤ (fixedBy X bG)ᶜ.ncard := by
    rw [Set.ncard_compl, hbfix, Nat.card_eq_fintype_card]
    omega
  obtain ⟨b', hb'N, hb'2, hb'ne, hb'fix, hb'two⟩ := OyamaSixNormalizerRepresentative.exists_conjugate
    G X h4 s hs S hcardQ heven bG hbG2 hbmoved
  have hb'six : (fixedBy X b').ncard = 6 := hb'fix.trans hbfix
  have hb'twoS : (fixedBy X b' ∩ fixedPoints S X).ncard = 2 := by
    rw [← OyamaSixElementary.fixedPoints_image G X H (S : Subgroup H)]
    exact hb'two
  rcases OyamaSixOrderUpper.involution_fixed_two_or_six G X h4 s hs S hfree hcard himage a ha with
    hafix | hafix
  · have hamoved : 4 ≤ (fixedBy X a)ᶜ.ncard := by
      rw [Set.ncard_compl, hafix, Nat.card_eq_fintype_card]
      omega
    obtain ⟨a', ha'N, ha'2, ha'ne, ha'fix, _⟩ := OyamaSixNormalizerRepresentative.exists_conjugate
      G X h4 s hs S hcardQ heven a ha hamoved
    obtain ⟨g, _, hg⟩ := SixteenNormalizerInvolutions.exists_conjugator_of_nontrivial_image
      G X s S hQcomm hsq hS hfree a' b' ha'N hb'N ha'2 hb'2 hcardQ himage ha'ne hb'ne hb'six hb'twoS
    have heq : (fixedBy X b').ncard = (fixedBy X a').ncard := by
      rw [← hg, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact Nat.card_congr (SemiregularSylowFixedSet.fixedByConjugateEquiv G X b' g)
    omega
  · exact hafix

end FiveTransitive.OyamaSixOrderSixteen

end CFSG
