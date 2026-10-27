module

public import CFSG.Permutation.FiveTransitive.CyclicTwoCommutativeActual
public import CFSG.Permutation.FiveTransitive.CyclicTwoComplementCounts
public import CFSG.Permutation.FiveTransitive.AbelianSixteenExceptionalOrbit

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicTwoActualSemiregular

open MulAction FixedNormalizerAction

theorem exists_sylow_semiregular
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (hQ : Nat.card Q = 2)
    (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (v : Normalizer Q) (hv : orderOf v.val = 2)
    (hlocal : (fixedBy X v.val ∩ fixedPoints Q X).ncard = 3)
    (hfour : (fixedBy X v.val \ fixedPoints Q X).ncard = 4)
    (hzero : ∀ (A : Subgroup G), Q ≤ A → IsPGroup 2 A →
      ∀ u : Normalizer Q, u.val ∈ A → u.val ∉ Q →
      (fixedBy X u.val ∩ fixedPoints Q X).ncard = 5 →
      Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) = 0) :
    ∃ (e : Fin 6 ↪ Fixed (X := X) Q)
      (P : Sylow 2 ((ThreeSwapTwoGroup.subgroup e).comap
        (toPermHom (Normalizer Q) (Fixed (X := X) Q)))),
      let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
      let V := ThreeSwapTwoGroup.subgroup e
      let B := SylowPreimageNormalizer.ambient f V P
      f v = Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3) ∧
      IsPGroup 2 B ∧ Inside Q ≤ B ∧ v ∈ B ∧ B.map f = V ∧ B ⊓ f.ker = Inside Q ∧
      IsMulCommutative B ∧ Nat.card B = 16 ∧
      (∀ (g : B) (t : NormalizerFixedComplement.Domain (X := X) Q),
        t ∉ fixedBy (NormalizerFixedComplement.Domain (X := X) Q) v →
        g • t = t → g = 1) ∧
      (∀ (g : B) (t : X), t ∉ fixedPoints Q X → v.val • t ≠ t →
        g.val.val • t = t → g = 1) := by
  classical
  obtain ⟨e, P, hvf, hp, hIB, hvB, hm, hk, _, _, a, hane, _, _, hsingle, _,
    x, y, z, hx, hy, hz, _, _, _, _, hcomm, hcard⟩ :=
    CyclicTwoCommutativeActual.exists_sylow heven hdegree hmax Q hQ hseven S hS himage v hv hlocal hzero
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let V := ThreeSwapTwoGroup.subgroup e
  let B := SylowPreimageNormalizer.ambient f V P
  let D := NormalizerFixedComplement.Domain (X := X) Q
  let _ : CommGroup B := { (inferInstance : Group B) with mul_comm := isMulCommutative_iff.mp hcomm }
  have hx2 := hsingle x (e 0) (e 1) (e.injective.ne (by decide)) hx
  have hy2 := hsingle y (e 2) (e 3) (e.injective.ne (by decide)) hy
  have hz2 := hsingle z (e 4) (e 5) (e.injective.ne (by decide)) hz
  obtain ⟨hxo, hxfree, hsquare, hbound⟩ := CyclicTwoComplementCounts.counts
    hmax Q hQ hseven hfree B hcomm e hm hk a hane x y z hx hy hz hx2 hy2 hz2
  let vB : B := ⟨v, hvB⟩
  have hvne : vB ≠ 1 := by
    intro he
    have hv1 : v.val = 1 := congrArg (fun b : B => b.val.val) he
    rw [hv1, orderOf_one] at hv
    omega
  have hvfour : (fixedBy D vB).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact (NormalizerFixedComplement.fixed_card Q v).trans hfour
  have hfreeB := AbelianSixteenExceptionalOrbit.semiregular_off_fixed
    hcard x hxo hxfree hsquare hbound vB hvne hvfour
  refine ⟨e, P, hvf, hp, hIB, hvB, hm, hk, hcomm, hcard, hfreeB, ?_⟩
  intro g t ht hvnot hgt
  apply hfreeB g ⟨t, ht⟩
  · intro hh
    exact hvnot (congrArg Subtype.val hh)
  · exact Subtype.ext hgt

end FiveTransitive.CyclicTwoActualSemiregular

end CFSG
