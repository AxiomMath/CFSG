module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG

namespace FiveTransitive.NormalizerOrbitPermutation

open MulAction

variable {G Y : Type*} [Group G] [MulAction G Y]

@[expose] def orbitMap (Q : Subgroup G) (x : Subgroup.normalizer (Q : Set G)) :
    orbitRel.Quotient Q Y → orbitRel.Quotient Q Y :=
  Quotient.map (fun y : Y => x.val • y) (by
    intro y z hyz
    obtain ⟨q, hq⟩ := mem_orbit_iff.mp hyz
    let r : Q := ⟨x.val * q.val * x.val⁻¹,
      (Subgroup.mem_normalizer_iff.mp x.property q.val).mp q.property⟩
    apply mem_orbit_iff.mpr
    refine ⟨r, ?_⟩
    change (x.val * q.val * x.val⁻¹) • (x.val • z) = x.val • y
    rw [mul_smul, mul_smul, inv_smul_smul]
    exact congrArg (fun t : Y => x.val • t) hq)

@[simp] theorem orbitMap_mk (Q : Subgroup G) (x : Subgroup.normalizer (Q : Set G)) (y : Y) :
    orbitMap Q x (Quotient.mk'' y) = Quotient.mk'' (x.val • y) := rfl

@[expose] def orbitPerm (Q : Subgroup G) (x : Subgroup.normalizer (Q : Set G)) : Equiv.Perm (orbitRel.Quotient Q Y) where
  toFun := orbitMap Q x
  invFun := orbitMap Q x⁻¹
  left_inv O := Quotient.inductionOn O (fun y => by simp only [orbitMap_mk, Subgroup.coe_inv, inv_smul_smul])
  right_inv O := Quotient.inductionOn O (fun y => by simp only [orbitMap_mk, Subgroup.coe_inv, smul_inv_smul])

@[simp] theorem orbitPerm_mk (Q : Subgroup G) (x : Subgroup.normalizer (Q : Set G)) (y : Y) :
    orbitPerm Q x (Quotient.mk'' y) = Quotient.mk'' (x.val • y) := rfl

theorem fixed_iff_transporter (Q : Subgroup G) (x : Subgroup.normalizer (Q : Set G)) (y : Y) :
    orbitPerm Q x (Quotient.mk'' y) = Quotient.mk'' y ↔
      ∃ q : Q, (q.val * x.val) • y = y := by
  rw [orbitPerm_mk]
  constructor
  · intro h
    have hh : y ∈ orbit Q (x.val • y) := Quotient.exact h.symm
    obtain ⟨q, hq⟩ := mem_orbit_iff.mp hh
    refine ⟨q, ?_⟩
    change q.val • (x.val • y) = y at hq
    simpa only [mul_smul] using hq
  · rintro ⟨q, hq⟩
    apply Eq.symm
    apply Quotient.sound
    apply mem_orbit_iff.mpr
    refine ⟨q, ?_⟩
    change q.val • (x.val • y) = y
    simpa only [mul_smul] using hq

end FiveTransitive.NormalizerOrbitPermutation

end CFSG
