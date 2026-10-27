module

public import CFSG.Permutation.FiveTransitive.NormalizerOneOrbitRepresentative
public import CFSG.Permutation.FiveTransitive.NormalizerOneOrbitCardFour
public import CFSG.Permutation.FiveTransitive.ThreeSwapCompatibleSylow
public import CFSG.Permutation.FiveTransitive.OneOrbitElementaryExtension
public import CFSG.Permutation.FiveTransitive.OneOrbitElementarySemiregular

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.NormalizerOneOrbitSemiregularActual

open MulAction FixedNormalizerAction

theorem exists_semiregular
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q A : Subgroup G) (hQA : Q ≤ A) (hA : IsPGroup 2 A)
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (x : Normalizer Q) (hx : x.val ∈ A) (hxQ : x.val ∉ Q)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5)
    (hone : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) = 1) :
    ∃ q : Inside Q, let v := q.val * x
    ∃ (e : Fin 6 ↪ Fixed (X := X) Q)
      (P : Sylow 2 ((ThreeSwapTwoGroup.subgroup e).comap
        (toPermHom (Normalizer Q) (Fixed (X := X) Q)))),
      let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
      let V := ThreeSwapTwoGroup.subgroup e
      let B := SylowPreimageNormalizer.ambient f V P
      ∃ (a : Inside Q) (K : Subgroup (Normalizer Q))
        (z : NormalizerFixedComplement.Domain (X := X) Q),
      let O := orbit Q z.val
      v.val ∈ A ∧ v.val ∉ Q ∧ orderOf v.val = 2 ∧
      f v = Equiv.swap (e 0) (e 1) ∧
      NormalizerSevenOrbitCount.orbitPerm (X := X) Q v =
        NormalizerSevenOrbitCount.orbitPerm (X := X) Q x ∧
      IsPGroup 2 B ∧ Inside Q ≤ B ∧ v ∈ B ∧ B.map f = V ∧
      B ⊓ f.ker = Inside Q ∧ (f.comp B.subtype).ker = (Inside Q).subgroupOf B ∧
      (Subgroup.normalizer (B : Set (Normalizer Q))).map f =
        Subgroup.normalizer (V : Set (Equiv.Perm (Fixed (X := X) Q))) ∧
      orderOf a.val.val = 2 ∧ Commute a.val.val v.val ∧
      K = Subgroup.closure (insert a.val ((stabilizer B z).map B.subtype : Set (Normalizer Q))) ∧
      K ≤ B ∧ a.val ∈ K ∧ v ∈ K ∧ IsPGroup 2 K ∧
      (∀ k : K, k ^ 2 = 1) ∧ IsMulCommutative K ∧ 8 ∣ Nat.card K ∧ K.map f = V ∧
      Nat.card Q = 4 ∧ v • z = z ∧ O.ncard = 4 ∧ O ⊆ (fixedPoints Q X)ᶜ ∧
      O = (fixedBy X v.val \ fixedPoints Q X) ∪
        (fixedBy X (a.val.val * v.val) \ fixedPoints Q X) ∧
      (∀ (k : K) (t : X), t ∈ O → k.val.val • t ∈ O) ∧
      (∀ (u : B) (t : X), t ∉ fixedPoints Q X ∪ O → u.val.val • t = t → u = 1) ∧
      ∃ y w : K, f y.val = Equiv.swap (e 2) (e 3) ∧ f w.val = Equiv.swap (e 4) (e 5) := by
  classical
  obtain ⟨q, hvA, hvQ, hvorder, hvlocal, hsame, hC, _, z, hz⟩ :=
    NormalizerOneOrbitRepresentative.exists_involution heven hdegree hmax Q A hQA hA
      hQ hne hseven hfree x hx hxQ hlocal (by omega)
  let v : Normalizer Q := q.val * x
  have hvone : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q v)) ≤ 1 := by rw [hsame, hone]
  have hseven' : Nat.card (Fixed (X := X) Q) = 7 := by simpa only [fixed_eq Q] using hseven
  obtain ⟨e, P, hvf, _, hB, hIB, hvB, hmap, hker, hrker, hnormal, _⟩ :=
    ThreeSwapCompatibleSylow.exists_three_swaps Q hseven' S hS himage A hA hQA v hvA hvlocal
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let B := SylowPreimageNormalizer.ambient f (ThreeSwapTwoGroup.subgroup e) P
  obtain ⟨a, K, haorder, hav, hKdef, hKB, haK, hvK, _, hKp, hK2, hKcomm, hK8, hKmap,
      hOrbit, y, w, hy, hw⟩ :=
    OneOrbitElementaryExtension.exists_extension Q e B hmap hker hfree ⟨v, hvB⟩ hvf hvone z hz hC
  let aK : K := ⟨a.val, haK⟩
  let vK : K := ⟨v, hvK⟩
  have hane : aK ≠ 1 := by
    intro he
    have hh : a.val.val = 1 := congrArg (fun k : K => k.val.val) he
    rw [hh, orderOf_one] at haorder
    omega
  have hQfour : Nat.card Q = 4 :=
    NormalizerOneOrbitCardFour.card_four_of_elementary heven hdegree hmax
      Q hQ hseven' hfree K hK2 hKcomm hK8 aK vK y w a.property hane e hvf hy hw hvone z hz hOrbit
  obtain ⟨hOcard, hOoutside, hOeq, hsemi⟩ := OneOrbitElementarySemiregular.semiregular
    heven hdegree hmax Q hQ hne hQfour hseven' hfree B K hB hKB hker
    (hKmap.trans hmap.symm) hK2 hKcomm aK vK y w a.property hane e hvf hy hw hvone z hz
  exact ⟨q, e, P, a, K, z, hvA, hvQ, hvorder, hvf, hsame, hB, hIB, hvB, hmap,
    hker, hrker, hnormal, haorder, hav, hKdef, hKB, haK, hvK, hKp, hK2, hKcomm,
    hK8, hKmap, hQfour, hz, hOcard, hOoutside, hOeq, hOrbit, hsemi, y, w, hy, hw⟩

end FiveTransitive.NormalizerOneOrbitSemiregularActual

end CFSG
