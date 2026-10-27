module

public import CFSG.Permutation.FiveTransitive.ThreeSwapElementaryActual
public import CFSG.Permutation.FiveTransitive.ThreeSwapEvenCounts
public import CFSG.Permutation.FiveTransitive.ThreeSwapLocalFixedCounts
public import CFSG.Permutation.FiveTransitive.ElementaryShortOrbitSemiregular

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.ThreeSwapSemiregularActual

open MulAction FixedNormalizerAction

theorem exists_semiregular
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (hQ : Nat.card Q = 2) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (A : Subgroup G) (hA : IsPGroup 2 A) (hQA : Q ≤ A)
    (x : Normalizer Q) (hxA : (x : G) ∈ A) (hx : orderOf (x : G) = 2)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5)
    (houtside : (fixedBy X x.val \ fixedPoints Q X).ncard = 2) :
    ∃ (e : Fin 6 ↪ Fixed (X := X) Q)
      (P : Sylow 2 ((ThreeSwapTwoGroup.subgroup e).comap
        (toPermHom (Normalizer Q) (Fixed (X := X) Q)))),
      let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
      let V := ThreeSwapTwoGroup.subgroup e
      let B := SylowPreimageNormalizer.ambient f V P
      f x = Equiv.swap (e 0) (e 1) ∧ IsPGroup 2 B ∧ Inside Q ≤ B ∧ x ∈ B ∧
      B.map f = V ∧ B ⊓ f.ker = Inside Q ∧
      (f.comp B.subtype).ker = (Inside Q).subgroupOf B ∧
      (Subgroup.normalizer (B : Set (Normalizer Q))).map f =
        Subgroup.normalizer (V : Set (Equiv.Perm (Fixed (X := X) Q))) ∧
      (∀ g : B, g ^ 2 = 1) ∧ IsMulCommutative B ∧
      ∃ E : Set X, E.ncard = 4 ∧ E ⊆ (fixedPoints Q X)ᶜ ∧
        ∀ g : B, g ≠ 1 → ∀ t ∉ fixedPoints Q X ∪ E, (g.val : G) • t ≠ t := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, P, hxf, hp, hIP, hxP, hm, hk, hkr, hn, y, z, hyf, hzf,
    hxord, hyord, hzord, hxy, hxz, hyz, hQcomm, a, haI, haord, hagen, hgen, hsq, habel⟩ :=
    ThreeSwapElementaryActual.exists_elementary_lifts Q hQ hseven S hS himage
      A hA hQA x hxA hx hlocal houtside
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let V := ThreeSwapTwoGroup.subgroup e
  let B := SylowPreimageNormalizer.ambient f V P
  change ∀ g : B, g ^ 2 = 1 at hsq
  change IsMulCommutative B at habel
  let _ : CommGroup B := { (inferInstance : Group B) with
    mul_comm := isMulCommutative_iff.mp habel }
  let aB : B := ⟨a, hIP haI⟩
  let b : B := ⟨x, hxP⟩
  let c : B := y
  let d : B := z
  let aQ : Q := ⟨a.val, haI⟩
  have haQne : aQ ≠ 1 := by
    intro he
    have haone : a = 1 := Subtype.ext (congrArg (fun q : Q => (q : G)) he)
    rw [haone, orderOf_one] at haord
    omega
  have hfix : fixedBy X aB = fixedPoints Q X := by
    ext w
    constructor
    · intro hw
      rw [mem_fixedPoints]
      intro q
      rcases Research.OddIndexTwoConjugacy.eq_one_or_eq_of_natCard_eq_two hQ aQ haQne q with he | he
      · rw [he, one_smul]
      · rw [he]
        exact hw
    · intro hw
      exact mem_fixedPoints.mp hw aQ
  have hfixseven : (fixedBy X aB).ncard = 7 := by
    rw [hfix]
    simpa only [Nat.card_coe_set_eq, fixed_eq] using hseven
  have hB2 (g : B) : g * g = 1 := by simpa only [pow_two] using hsq g
  have hBmax (g : B) (hg : g ≠ 1) : (fixedBy X g).ncard ≤ 7 := by
    have hp : (g.val : G) ^ 2 = 1 :=
      congrArg (fun b : B => (b.val : G)) (hsq g)
    have hne : (g.val : G) ≠ 1 := by
      intro h
      exact hg (Subtype.ext (Subtype.ext h))
    exact hmax (g.val : G) (orderOf_eq_prime hp hne)
  have hcount (u : B) (v w : Fixed (X := X) Q) (hne : v ≠ w)
      (hu : f u.val = Equiv.swap v w) :
      (fixedBy X u \ fixedBy X aB).ncard = 2 ∧
        (fixedBy X (aB * u) \ fixedBy X aB).ncard = 2 := by
    rw [hfix]
    constructor
    · have h := ThreeSwapEvenCounts.coset_outside_two heven hdegree hmax Q hseven
        B hIP hsq u v w hne hu (1 : Inside Q)
      change (fixedBy X (u.val : G) \ fixedPoints Q X).ncard = 2
      simpa only [OneMemClass.coe_one, one_mul] using h
    · exact ThreeSwapEvenCounts.coset_outside_two heven hdegree hmax Q hseven
        B hIP hsq u v w hne hu ⟨a, haI⟩
  have hb := hcount b (e 0) (e 1) (e.injective.ne (by decide)) hxf
  have hc := hcount c (e 2) (e 3) (e.injective.ne (by decide)) hyf
  have hd := hcount d (e 4) (e 5) (e.injective.ne (by decide)) hzf
  have hpair := ThreeSwapLocalFixedCounts.actual_pair_counts Q hseven e x y.val z.val hxf hyf hzf
  have hbc : (fixedBy X (b * c) ∩ fixedBy X aB).ncard = 3 := by
    rw [hfix]; exact hpair.1
  have hbd : (fixedBy X (b * d) ∩ fixedBy X aB).ncard = 3 := by
    rw [hfix]; exact hpair.2.1
  have hcd : (fixedBy X (c * d) ∩ fixedBy X aB).ncard = 3 := by
    rw [hfix]; exact hpair.2.2
  obtain ⟨hE, hsemi⟩ := ElementaryShortOrbitSemiregular.semiregular hB2 hBmax
    aB b c d hfixseven hb.1 hb.2 hc.1 hc.2 hd.1 hd.2 hbc hbd hcd
  let E := (fixedBy X b \ fixedBy X aB) ∪ (fixedBy X (aB * b) \ fixedBy X aB)
  refine ⟨e, P, hxf, hp, hIP, hxP, hm, hk, hkr, hn, hsq, habel, E, hE, ?_, ?_⟩
  · intro t ht
    rcases ht with ht | ht
    · rw [hfix] at ht
      exact ht.2
    · rw [hfix] at ht
      exact ht.2
  · intro g hg t ht
    apply hsemi g hg t
    change t ∉ fixedBy X aB ∪ E
    rw [hfix]
    exact ht

end FiveTransitive.ThreeSwapSemiregularActual

end CFSG
