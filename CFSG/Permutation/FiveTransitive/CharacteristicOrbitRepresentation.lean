module

public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG

namespace FiveTransitive.CharacteristicOrbitRepresentation

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] def inclusion (T : Subgroup G) : T →* Subgroup.normalizer (T : Set G) where
  toFun t := ⟨t.val,T.le_normalizer t.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def orbitMap (T : Subgroup G) (C : Subgroup T) [C.Characteristic]
    (g : Subgroup.normalizer (T : Set G)) :
    orbitRel.Quotient C X → orbitRel.Quotient C X :=
  Quotient.map (fun x : X => g.val • x) (by
    intro x y hxy
    obtain ⟨c,hc⟩ := mem_orbit_iff.mp hxy
    let e := CharacteristicAutomorphism.restrict C (T.normalizerMonoidHom g)
    apply mem_orbit_iff.mpr
    refine ⟨e c,?_⟩
    change ((T.normalizerMonoidHom g c.val : T) : G) • (g.val • y) = g.val • x
    rw [T.normalizerMonoidHom_apply_apply_coe,mul_smul,mul_smul,inv_smul_smul]
    exact congrArg (fun z : X => g.val • z) hc)

@[simp] theorem orbitMap_mk (T : Subgroup G) (C : Subgroup T) [C.Characteristic]
    (g : Subgroup.normalizer (T : Set G)) (x : X) :
    orbitMap T C g (Quotient.mk'' x) = Quotient.mk'' (g.val • x) := rfl

@[expose] def orbitPerm (T : Subgroup G) (C : Subgroup T) [C.Characteristic]
    (g : Subgroup.normalizer (T : Set G)) : Equiv.Perm (orbitRel.Quotient C X) where
  toFun := orbitMap T C g
  invFun := orbitMap T C g⁻¹
  left_inv O := Quotient.inductionOn O (fun x => by
    simp only [orbitMap_mk,Subgroup.coe_inv,inv_smul_smul])
  right_inv O := Quotient.inductionOn O (fun x => by
    simp only [orbitMap_mk,Subgroup.coe_inv,smul_inv_smul])

@[simp] theorem orbitPerm_mk (T : Subgroup G) (C : Subgroup T) [C.Characteristic]
    (g : Subgroup.normalizer (T : Set G)) (x : X) :
    orbitPerm T C g (Quotient.mk'' x) = Quotient.mk'' (g.val • x) := rfl

@[expose] def orbitHom (T : Subgroup G) (C : Subgroup T) [C.Characteristic] :
    Subgroup.normalizer (T : Set G) →* Equiv.Perm (orbitRel.Quotient C X) where
  toFun := orbitPerm T C
  map_one' := by
    apply Equiv.ext
    intro O
    refine Quotient.inductionOn O ?_
    intro x
    change Quotient.mk'' ((1 : G) • x) = Quotient.mk'' x
    rw [one_smul]
  map_mul' a b := by
    apply Equiv.ext
    intro O
    refine Quotient.inductionOn O ?_
    intro x
    change Quotient.mk'' ((a.val * b.val) • x) = Quotient.mk'' (a.val • (b.val • x))
    rw [mul_smul]

theorem range_pretransitive (T : Subgroup G) (C : Subgroup T) [C.Characteristic]
    (htrans : IsPretransitive T X) :
    IsPretransitive ((orbitHom (X := X) T C).comp (inclusion T)).range
      (orbitRel.Quotient C X) := by
  constructor
  intro u v
  refine Quotient.inductionOn₂ u v ?_
  intro x y
  obtain ⟨t,ht⟩ := htrans.exists_smul_eq x y
  refine ⟨⟨orbitHom T C (inclusion T t),⟨t,rfl⟩⟩,?_⟩
  change Quotient.mk'' (t.val • x) = Quotient.mk'' y
  exact congrArg Quotient.mk'' ht

theorem mem_normalizer_range (T : Subgroup G) (C : Subgroup T) [C.Characteristic]
    (g : Subgroup.normalizer (T : Set G)) :
    orbitHom (X := X) T C g ∈ Subgroup.normalizer
      ((((orbitHom (X := X) T C).comp (inclusion T)).range) : Set (Equiv.Perm (orbitRel.Quotient C X))) := by
  let f := orbitHom (X := X) T C
  let e := T.normalizerMonoidHom g
  have hc (t : T) : f (inclusion T (e t)) = f g * f (inclusion T t) * (f g)⁻¹ := by
    rw [← map_inv,← map_mul,← map_mul]
    apply congrArg f
    apply Subtype.ext
    exact T.normalizerMonoidHom_apply_apply_coe g t
  apply Subgroup.mem_normalizer_iff.mpr
  intro a
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨e t,hc t⟩
  · rintro ⟨t,ht⟩
    refine ⟨e.symm t,?_⟩
    change f (inclusion T t) = f g * a * (f g)⁻¹ at ht
    have hh := hc (e.symm t)
    rw [e.apply_symm_apply,ht] at hh
    exact mul_left_cancel (mul_right_cancel hh.symm)

end FiveTransitive.CharacteristicOrbitRepresentation

end CFSG
