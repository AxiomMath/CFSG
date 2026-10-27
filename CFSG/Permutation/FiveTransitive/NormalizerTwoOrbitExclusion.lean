module

public import CFSG.Permutation.FiveTransitive.NormalizerInvolutionThreeSwaps
public import CFSG.Permutation.FiveTransitive.NormalizerSemiregularOutsideBound
public import CFSG.Permutation.FiveTransitive.HighDegreeSaturatedFourShortOrbits
public import CFSG.Permutation.FiveTransitive.ThreeSwapSemiregularActual

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.NormalizerTwoOrbitExclusion

open MulAction FixedNormalizerAction

private theorem false_of_semiregular_sylow
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hQ : Nat.card Q = 2)
    (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (himage : Image (X := X) Q = ⊤)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (e : Fin 6 ↪ Fixed (X := X) Q)
    (P : Sylow 2 ((ThreeSwapTwoGroup.subgroup e).comap
      (toPermHom (Normalizer Q) (Fixed (X := X) Q))))
    (hQB : Inside Q ≤ SylowPreimageNormalizer.ambient
      (toPermHom (Normalizer Q) (Fixed (X := X) Q)) (ThreeSwapTwoGroup.subgroup e) P)
    (E : Set X) (hE : E.ncard ≤ 4)
    (hsemi : ∀ (b : SylowPreimageNormalizer.ambient
      (toPermHom (Normalizer Q) (Fixed (X := X) Q)) (ThreeSwapTwoGroup.subgroup e) P)
      (z : X), z ∉ fixedPoints Q X → z ∉ E → b.val.val • z = z → b = 1)
    (u : Normalizer Q) (hu : orderOf u.val = 2) (huQ : u.val ∉ Q)
    (hfour : 4 ≤ Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u))) : False := by
  obtain ⟨v, _, hvQ, hcount⟩ :=
    NormalizerInvolutionThreeSwaps.exists_element Q hseven himage e P u hu huQ
  have hle := NormalizerSemiregularOutsideBound.fixed_orbits_le_two Q hQ hfree
    _ hQB E hE hsemi v.val v.property hvQ
  rw [hcount] at hle
  omega

theorem not_two_fixed_orbits
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
    : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) ≠ 2 := by
  intro horbits
  obtain ⟨hQcard, hxorder, hcoset⟩ := NormalizerTwoOrbitSeed.card_two_involution_coset
    heven hdegree hmax Q A hQA hA hQ hne hseven hfree S hS himage x hx hxQ hlocal horbits
  have hseven' : Nat.card (Fixed (X := X) Q) = 7 := by
    simpa only [fixed_eq Q] using hseven
  have hout : (fixedBy X x.val \ fixedPoints Q X).ncard = 2 := by
    simpa only [OneMemClass.coe_one, one_mul] using hcoset 1
  obtain ⟨e, P, _, _, hIP, _, _, _, _, _, _, _, E, hE, _, hsemi⟩ :=
    ThreeSwapSemiregularActual.exists_semiregular (fun g => by
      convert heven g using 1
      congr 2
      exact Subsingleton.elim _ _) hdegree hmax Q hQcard hseven'
      S hS himage A hA hQA x hx hxorder hlocal hout
  obtain ⟨_, _, u, _, hu, huQ, _, _, hfour, _⟩ :=
    HighDegreeSaturatedFourShortOrbits.exists_four_short_orbits
      hcard h5 heven hdegree hmax Q A hQA hA hQ hne hseven hfree
      S hS himage x hx hxQ hlocal horbits
  apply false_of_semiregular_sylow Q hQcard hseven' himage hfree e P hIP E hE.le
    ?_ u hu huQ hfour
  intro b z hzQ hzE hbz
  by_contra hb
  exact hsemi b hb z (fun hz => hz.elim hzQ hzE) hbz

end FiveTransitive.NormalizerTwoOrbitExclusion

end CFSG
