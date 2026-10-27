module

public import CFSG.Permutation.FiveTransitive.CharacteristicOrbitRepresentation
public import CFSG.Permutation.FiveTransitive.CoprimeCentralizerOrbit
public import CFSG.Permutation.FiveTransitive.SixteenTwoGroupRegular

public section

namespace CFSG

namespace FiveTransitive.ThirtyTwoTwoGroupPairQuotient

open MulAction

theorem data
    {X : Type*} [Finite X] (hX : Nat.card X = 32)
    (R : Subgroup (Equiv.Perm X)) (hR : IsPGroup 2 R)
    (htrans : IsPretransitive R X)
    (g : Subgroup.normalizer (R : Set (Equiv.Perm X))) (hg : g ^ 5 = 1)
    (hfixed : Nat.card (Function.fixedPoints g.val) = 2)
    (hZ : Nat.card (Subgroup.center R) = 2) :
    let Z := Subgroup.center R
    let O := orbitRel.Quotient Z X
    let b := CharacteristicOrbitRepresentation.orbitHom (X := X) R Z
    Nat.card O = 16 ∧ Nat.card (Function.fixedPoints (b g)) = 1 ∧
      Nat.card (b.comp (CharacteristicOrbitRepresentation.inclusion R)).range = 16 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let Z := Subgroup.center R
  let O := orbitRel.Quotient Z X
  let b := CharacteristicOrbitRepresentation.orbitHom (X := X) R Z
  change Nat.card Z = 2 at hZ
  change Nat.card O = 16 ∧ Nat.card (Function.fixedPoints (b g)) = 1 ∧
    Nat.card (b.comp (CharacteristicOrbitRepresentation.inclusion R)).range = 16
  have hO : Nat.card O = 16 := by
    have hm := TransitiveCenterFree.card_mul_orbits htrans
    change Nat.card Z * Nat.card O = Nat.card X at hm
    rw [hZ,hX] at hm
    omega
  let f : Subgroup.normalizer (R : Set (Equiv.Perm X)) →* MulAut Z :=
    (CharacteristicAutomorphism.restrict Z).comp R.normalizerMonoidHom
  have hfa : f g = 1 := by
    by_contra hn
    have hp : (f g) ^ 5 = 1 := by rw [← map_pow,hg,map_one]
    have hh := TwoGroupFiveAutomorphism.card_eq_sixteen_of_order_five Z
      (hR.to_subgroup Z) (by omega) (f g) (orderOf_eq_prime hp hn)
    omega
  have hcomm (c : Z) : Commute g.val c.val.val := by
    have hh := congrArg (fun a : MulAut Z => (a c).val.val) hfa
    change (R.normalizerMonoidHom g c.val : Equiv.Perm X) = c.val.val at hh
    rw [R.normalizerMonoidHom_apply_apply_coe] at hh
    exact (mul_inv_eq_iff_eq_mul).mp hh
  have hfix (x : X) : b g (Quotient.mk'' x) = Quotient.mk'' x ↔ g.val x = x := by
    constructor
    · intro hx
      have horbit : g.val • x ∈ orbit Z x := Quotient.exact hx
      obtain ⟨c,hc⟩ := mem_orbit_iff.mp horbit
      have hgval : g.val ^ 5 = 1 := congrArg Subtype.val hg
      have hcop : (orderOf c.val.val).Coprime (orderOf g.val) := by
        rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe]
        exact Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hgval)
          ((hR.to_subgroup Z).orderOf_coprime (by decide : Nat.Coprime 2 5) c)
      exact CoprimeCentralizerOrbit.fixed_of_commute g.val c.val.val (hcomm c) hcop x hc.symm
    · intro hx
      change Quotient.mk'' (g.val x) = Quotient.mk'' x
      rw [hx]
  let e : {x : X // b g (Quotient.mk'' x) = Quotient.mk'' x} ≃ Function.fixedPoints g.val :=
    { toFun := fun x => ⟨x.val,(hfix x.val).mp x.property⟩
      invFun := fun x => ⟨x.val,(hfix x.val).mpr x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcount := FreeActionTransporterCount.card_orbit_preimage
    (TransitiveCenterFree.free htrans) (fun o : O => b g o = o)
  rw [Nat.card_congr e,hfixed,hZ] at hcount
  have hfixO : Nat.card (Function.fixedPoints (b g)) = 1 := by
    change 2 = 2 * Nat.card (Function.fixedPoints (b g)) at hcount
    omega
  let rho := b.comp (CharacteristicOrbitRepresentation.inclusion R)
  let H := rho.range
  have hH : IsPGroup 2 H := hR.of_surjective rho.rangeRestrict rho.rangeRestrict_surjective
  have hHtrans : IsPretransitive H O :=
    CharacteristicOrbitRepresentation.range_pretransitive R Z htrans
  have hbN : b g ∈ Subgroup.normalizer (H : Set (Equiv.Perm O)) :=
    CharacteristicOrbitRepresentation.mem_normalizer_range R Z g
  have hb5 : (b g) ^ 5 = 1 := by rw [← map_pow,hg,map_one]
  have hHcard := (SixteenTwoGroupRegular.of_normalizing_perm hO H hH hHtrans (b g) hbN hb5 hfixO).1
  exact ⟨hO,hfixO,hHcard⟩

end FiveTransitive.ThirtyTwoTwoGroupPairQuotient

end CFSG
