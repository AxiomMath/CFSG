module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerCompatibleSylow
public import CFSG.Permutation.FiveTransitive.ThreeSwapTwoGroup
public import CFSG.Permutation.FiveTransitive.FixedNormalizerLocalCard

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.ThreeSwapCompatibleSylow

open MulAction FixedNormalizerAction

theorem exists_three_swaps
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (A : Subgroup G) (hA : IsPGroup 2 A) (hQA : Q ≤ A)
    (x : Normalizer Q) (hxA : (x : G) ∈ A)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5) :
    ∃ (e : Fin 6 ↪ Fixed (X := X) Q)
      (P : Sylow 2 ((ThreeSwapTwoGroup.subgroup e).comap
        (toPermHom (Normalizer Q) (Fixed (X := X) Q)))),
      let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
      let V := ThreeSwapTwoGroup.subgroup e
      let B := SylowPreimageNormalizer.ambient f V P
      f x = Equiv.swap (e 0) (e 1) ∧ (∀ v : V, v ^ 2 = 1) ∧
      IsPGroup 2 B ∧ Inside Q ≤ B ∧ x ∈ B ∧ B.map f = V ∧ B ⊓ f.ker = Inside Q ∧
      (f.comp B.subtype).ker = (Inside Q).subgroupOf B ∧
      (Subgroup.normalizer (B : Set (Normalizer Q))).map f =
        Subgroup.normalizer (V : Set (Equiv.Perm (Fixed (X := X) Q))) ∧
      ∃ y z : B,
        f y.val = Equiv.swap (e 2) (e 3) ∧ f z.val = Equiv.swap (e 4) (e 5) := by
  classical
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  obtain ⟨e, he⟩ := ThreeSwapTwoGroup.exists_embedding (by omega : 6 ≤ Nat.card (Fixed (X := X) Q))
    (f x) (FixedNormalizerLocalCard.isSwap Q hseven x hlocal)
  let V := ThreeSwapTwoGroup.subgroup e
  obtain ⟨hV, hVsq⟩ := ThreeSwapTwoGroup.isTwoGroup e
  have hxV : f x ∈ V := by
    rw [he]
    apply Subgroup.subset_closure
    simp
  obtain ⟨P, hp, hIP, hxP, hm, hk, hkr, hn⟩ :=
    FixedNormalizerCompatibleSylow.exists_with_element Q S hS himage V hV A hA hQA x hxA hxV
  let B := SylowPreimageNormalizer.ambient f V P
  have hy : Equiv.swap (e 2) (e 3) ∈ B.map f := by
    rw [hm]
    apply Subgroup.subset_closure
    simp
  have hz : Equiv.swap (e 4) (e 5) ∈ B.map f := by
    rw [hm]
    apply Subgroup.subset_closure
    simp
  obtain ⟨y, hyB, hyf⟩ := hy
  obtain ⟨z, hzB, hzf⟩ := hz
  exact ⟨e, P, he, hVsq, hp, hIP, hxP, hm, hk, hkr, hn,
    ⟨⟨y, hyB⟩, ⟨z, hzB⟩, hyf, hzf⟩⟩

end FiveTransitive.ThreeSwapCompatibleSylow

end CFSG
