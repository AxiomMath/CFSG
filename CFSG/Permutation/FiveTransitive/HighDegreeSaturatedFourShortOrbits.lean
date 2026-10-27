module

public import CFSG.Permutation.FiveTransitive.NormalizerTwoOrbitSeed
public import CFSG.Permutation.FiveTransitive.HighDegreeFourShortOrbits

public section

namespace CFSG

namespace FiveTransitive.HighDegreeSaturatedFourShortOrbits

open MulAction FixedNormalizerAction Research.HallRegularOrbits

theorem exists_four_short_orbits
    {G X : Type} [Group G] [Finite G] [Fintype X] [DecidableEq X] [MulAction G X]
    (hcard : 28 ≤ Fintype.card X) (h5 : IsMultiplyPretransitive G X 5)
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q A : Subgroup G) (hQA : Q ≤ A) (hA : IsPGroup 2 A)
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (x : Normalizer Q) (hx : x.val ∈ A) (hxQ : x.val ∉ Q)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5)
    (horbits : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) = 2) :
    Nat.card Q = 2 ∧ ∃ (a : Q) (u : Normalizer Q),
      orderOf a.val = 2 ∧ orderOf u.val = 2 ∧ u.val ∉ Q ∧
      Commute u.val a.val ∧ Commute u.val x.val ∧
      4 ≤ Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) ∧
      ∃ z : X, (regularFourSet a.val x.val z).ncard = 4 ∧
        regularFourSet a.val x.val z ⊆
          (fixedBy X a.val ∪ fixedBy X x.val ∪ fixedBy X (a.val * x.val))ᶜ ∧
        ∀ y ∈ regularFourSet a.val x.val z, u.val • y = y := by
  obtain ⟨hQcard, hxorder, hcoset⟩ := NormalizerTwoOrbitSeed.card_two_involution_coset
    heven hdegree hmax Q A hQA hA hQ hne hseven hfree S hS himage x hx hxQ hlocal horbits
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 (by rw [hQcard])
  have haG : orderOf a.val = 2 :=
    (orderOf_injective Q.subtype Subtype.val_injective a).trans ha
  obtain ⟨u, hu2, huQ, hua, hux, hfour, hz⟩ := HighDegreeFourShortOrbits.exists_of_card_two
    hcard h5 hmax Q hQcard a haG hfree x hxorder hxQ hcoset
  exact ⟨hQcard, a, u, haG, hu2, huQ, hua, hux, hfour, hz⟩

end FiveTransitive.HighDegreeSaturatedFourShortOrbits

end CFSG
