module

public import CFSG.Permutation.FiveTransitive.FreeActionTransporterCount
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitPermutation
public import Mathlib.Data.Set.Card

public section

namespace CFSG

namespace FiveTransitive.SemiregularOutsideOrbitBound

open MulAction

private theorem card_mul_fixed_orbits_le
    {G Y : Type*} [Group G] [Finite G] [Finite Y] [MulAction G Y]
    (Q A : Subgroup G) (hQA : Q ≤ A)
    (hfree : ∀ (q : Q) (y : Y), q • y = y → q = 1)
    (E : Set Y)
    (hsemi : ∀ (a : A) (y : Y), y ∉ E → a • y = y → a = 1)
    (x : Subgroup.normalizer (Q : Set G)) (hxA : x.val ∈ A) (hxQ : x.val ∉ Q) :
    Nat.card Q * Nat.card (Function.fixedPoints
      (NormalizerOrbitPermutation.orbitPerm (Y := Y) Q x)) ≤ E.ncard := by
  let P := fun O : orbitRel.Quotient Q Y =>
    NormalizerOrbitPermutation.orbitPerm (Y := Y) Q x O = O
  have hE (y : Y) (hy : P (Quotient.mk'' y)) : y ∈ E := by
    by_contra hn
    obtain ⟨q, hq⟩ := (NormalizerOrbitPermutation.fixed_iff_transporter Q x y).mp hy
    let a : A := ⟨q.val * x.val, A.mul_mem (hQA q.property) hxA⟩
    have ha : a = 1 := hsemi a y hn hq
    have he : q.val * x.val = 1 := congrArg Subtype.val ha
    have hx : x.val = q.val⁻¹ := mul_left_cancel (he.trans (mul_inv_cancel q.val).symm)
    exact hxQ (hx ▸ Q.inv_mem q.property)
  let f : {y : Y // P (Quotient.mk'' y)} → E := fun y => ⟨y.val, hE y.val y.property⟩
  have hf : Function.Injective f := fun y z he => Subtype.ext (congrArg (fun t : E => t.val) he)
  have hle := Nat.card_le_card_of_injective f hf
  rw [FreeActionTransporterCount.card_orbit_preimage hfree P, Nat.card_coe_set_eq] at hle
  exact hle

theorem fixed_orbits_le_two
    {G Y : Type*} [Group G] [Finite G] [Finite Y] [MulAction G Y]
    (Q A : Subgroup G) (hQA : Q ≤ A) (hQ : Nat.card Q = 2)
    (hfree : ∀ (q : Q) (y : Y), q • y = y → q = 1)
    (E : Set Y) (hE : E.ncard ≤ 4)
    (hsemi : ∀ (a : A) (y : Y), y ∉ E → a • y = y → a = 1)
    (x : Subgroup.normalizer (Q : Set G)) (hxA : x.val ∈ A) (hxQ : x.val ∉ Q) :
    Nat.card (Function.fixedPoints (NormalizerOrbitPermutation.orbitPerm (Y := Y) Q x)) ≤ 2 := by
  have h := card_mul_fixed_orbits_le Q A hQA hfree E hsemi x hxA hxQ
  rw [hQ] at h
  omega

end FiveTransitive.SemiregularOutsideOrbitBound

end CFSG
