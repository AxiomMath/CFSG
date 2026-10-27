module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG

namespace FiveTransitive.FreeOrbitStabilizer

open MulAction

theorem bijective
    {G H Y : Type*} [Group G] [Group H] [MulAction G Y]
    (f : G →* H) (hf : Function.Surjective f) (Q : Subgroup G) (hker : f.ker = Q)
    (z : Y) (hfree : ∀ q : Q, q • z = z → q = 1)
    (horbit : ∀ g : G, g • z ∈ orbit Q z) :
    Function.Bijective (f.comp (stabilizer G z).subtype) := by
  constructor
  · intro a b he
    change f a.val = f b.val at he
    have hq : b.val⁻¹ * a.val ∈ Q := by
      rw [← hker]
      change f (b.val⁻¹ * a.val) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    have hfix : (⟨b.val⁻¹ * a.val, hq⟩ : Q) • z = z := by
      change (b.val⁻¹ * a.val) • z = z
      rw [mul_smul, a.property]
      exact (b⁻¹).property
    have htriv : b.val⁻¹ * a.val = 1 := congrArg Subtype.val (hfree _ hfix)
    exact Subtype.ext (inv_mul_eq_one.mp htriv).symm
  · intro h
    obtain ⟨g, hg⟩ := hf h
    obtain ⟨q, hq⟩ := mem_orbit_iff.mp (horbit g)
    have hfix : q.val⁻¹ * g ∈ stabilizer G z := by
      change (q.val⁻¹ * g) • z = z
      rw [mul_smul, ← hq]
      exact inv_smul_smul q.val z
    have hqf : f q.val = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [hker]
      exact q.property
    refine ⟨⟨q.val⁻¹ * g, hfix⟩, ?_⟩
    change f (q.val⁻¹ * g) = h
    rw [map_mul, map_inv, hqf, inv_one, one_mul, hg]

end FiveTransitive.FreeOrbitStabilizer

end CFSG
