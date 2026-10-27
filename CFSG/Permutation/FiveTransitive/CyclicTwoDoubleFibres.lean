module

public import CFSG.Permutation.FiveTransitive.ThreeSwapDoubleFibres
public import CFSG.Permutation.FiveTransitive.FixedNormalizerDoubleSwapSylow
public import CFSG.Permutation.FiveTransitive.NormalizerTwoElementInvolution

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicTwoDoubleFibres

open MulAction FixedNormalizerAction

theorem square_eq_one
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (Q : Subgroup G) (hQ : Nat.card Q = 2)
    (himage : Image (X := X) Q = ⊤)
    (e : Fin 6 ↪ Fixed (X := X) Q)
    (P : Sylow 2 ((ThreeSwapTwoGroup.subgroup e).comap
      (toPermHom (Normalizer Q) (Fixed (X := X) Q))))
    (hk : (SylowPreimageNormalizer.ambient
      (toPermHom (Normalizer Q) (Fixed (X := X) Q)) (ThreeSwapTwoGroup.subgroup e) P) ⊓
      (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (y : Normalizer Q) (hy : orderOf y.val = 2)
    (hyB : y ∈ SylowPreimageNormalizer.ambient
      (toPermHom (Normalizer Q) (Fixed (X := X) Q)) (ThreeSwapTwoGroup.subgroup e) P)
    (hyf : toPermHom (Normalizer Q) (Fixed (X := X) Q) y =
      Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3))
    (u : SylowPreimageNormalizer.ambient
      (toPermHom (Normalizer Q) (Fixed (X := X) Q)) (ThreeSwapTwoGroup.subgroup e) P)
    (hu : toPermHom (Normalizer Q) (Fixed (X := X) Q) u.val =
        Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3) ∨
      toPermHom (Normalizer Q) (Fixed (X := X) Q) u.val =
        Equiv.swap (e 0) (e 1) * Equiv.swap (e 4) (e 5) ∨
      toPermHom (Normalizer Q) (Fixed (X := X) Q) u.val =
        Equiv.swap (e 2) (e 3) * Equiv.swap (e 4) (e 5)) :
    u ^ 2 = 1 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp himage
  have hcentral : ∀ q : Inside Q, ∀ g : Normalizer Q,
      (q : Normalizer Q) * g = g * q := by
    intro q g
    apply Subtype.ext
    exact NormalizerTwoElementInvolution.central_of_card_two Q hQ g ⟨q.val.val, q.property⟩
  have hQsq : ∀ q : Inside Q, (q : Normalizer Q) ^ 2 = 1 := by
    intro q
    apply Subtype.ext
    let qQ : Q := ⟨q.val.val, q.property⟩
    have hqQ : qQ ^ 2 = 1 := by rw [← hQ]; exact pow_card_eq_one' (x := qQ)
    exact congrArg (fun q : Q => (q : G)) hqQ
  exact ThreeSwapDoubleFibres.square_eq_one f _ (Inside Q) hk hcentral hQsq e
    (SylowPreimageNormalizer.normalizer_map f hf (ThreeSwapTwoGroup.subgroup e)
      (ThreeSwapTwoGroup.isTwoGroup e).1 P) y hyB
    (Subtype.ext (hy ▸ pow_orderOf_eq_one y.val)) hyf u hu

theorem exists_sylow
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hQ : Nat.card Q = 2) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (y : Normalizer Q) (hy : orderOf y.val = 2)
    (hlocal : (fixedBy X y.val ∩ fixedPoints Q X).ncard = 3) :
    ∃ (e : Fin 6 ↪ Fixed (X := X) Q)
      (P : Sylow 2 ((ThreeSwapTwoGroup.subgroup e).comap
        (toPermHom (Normalizer Q) (Fixed (X := X) Q)))),
      let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
      let V := ThreeSwapTwoGroup.subgroup e
      let B := SylowPreimageNormalizer.ambient f V P
      f y = Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3) ∧
      IsPGroup 2 B ∧ Inside Q ≤ B ∧ y ∈ B ∧ B.map f = V ∧ B ⊓ f.ker = Inside Q ∧
      (Subgroup.normalizer (B : Set (Normalizer Q))).map f = Subgroup.normalizer (V : Set _) ∧
      (∃ x z : B, f x.val = Equiv.swap (e 0) (e 1) ∧ f z.val = Equiv.swap (e 4) (e 5)) ∧
      ∀ u : B,
        (f u.val = Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3) ∨
         f u.val = Equiv.swap (e 0) (e 1) * Equiv.swap (e 4) (e 5) ∨
         f u.val = Equiv.swap (e 2) (e 3) * Equiv.swap (e 4) (e 5)) → u ^ 2 = 1 := by
  classical
  obtain ⟨e, P, hyf, hp, hIP, hyP, hm, hk, hn, hxz⟩ :=
    FixedNormalizerDoubleSwapSylow.exists_sylow Q hseven S hS himage y hy hlocal
  exact ⟨e, P, hyf, hp, hIP, hyP, hm, hk, hn, hxz,
    fun u hu => square_eq_one Q hQ himage e P hk y hy hyP hyf u hu⟩

end FiveTransitive.CyclicTwoDoubleFibres

end CFSG
