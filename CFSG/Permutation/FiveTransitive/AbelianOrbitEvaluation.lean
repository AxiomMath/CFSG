module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG

namespace FiveTransitive.AbelianOrbitEvaluation

open MulAction

theorem orbit_subset_fixedBy
    {G X : Type*} [Group G] [IsMulCommutative G] [MulAction G X]
    (g : G) (x : X) (hx : g • x = x) : orbit G x ⊆ fixedBy X g := by
  intro y hy
  obtain ⟨a, rfl⟩ := mem_orbit_iff.mp hy
  change g • (a • x) = a • x
  rw [← mul_smul, (isMulCommutative_iff.mp (inferInstance : IsMulCommutative G)) g a, mul_smul, hx]

theorem orbit_disjoint_fixedPoints
    {G X : Type*} [Group G] [MulAction G X]
    (x : X) (hx : x ∉ fixedPoints G X) :
    Disjoint (fixedPoints G X) (orbit G x) := by
  apply Set.disjoint_left.mpr
  intro y hy hyo
  obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hyo
  have he : g • x = x := by
    simpa only [inv_smul_smul] using (hy g⁻¹).symm
  exact hx (he ▸ hy)

theorem orbit_disjoint_of_notMem
    {G X : Type*} [Group G] [MulAction G X]
    (x y : X) (hy : y ∉ orbit G x) : Disjoint (orbit G x) (orbit G y) := by
  apply Set.disjoint_left.mpr
  intro t htx hty
  obtain ⟨a, ha⟩ := mem_orbit_iff.mp htx
  obtain ⟨b, hb⟩ := mem_orbit_iff.mp hty
  apply hy
  apply mem_orbit_iff.mpr
  exact ⟨b⁻¹ * a, by rw [mul_smul, ha, ← hb, inv_smul_smul]⟩

theorem card_le_orbit
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (x : X) (hfree : ∀ g : G, g • x = x → g = 1) :
    Nat.card G ≤ Nat.card (orbit G x) := by
  let f : G → orbit G x := fun g => ⟨g • x, mem_orbit_iff.mpr ⟨g, rfl⟩⟩
  apply Nat.card_le_card_of_injective f
  intro a b hab
  have he : b⁻¹ * a = 1 := hfree _ (by
    rw [mul_smul, show a • x = b • x from congrArg Subtype.val hab, inv_smul_smul])
  exact (inv_mul_eq_one.mp he).symm

theorem card_le_three_orbits
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (x y z : X)
    (hfree : ∀ g : G, g • x = x → g • y = y → g • z = z → g = 1) :
    Nat.card G ≤ Nat.card (orbit G x) * Nat.card (orbit G y) * Nat.card (orbit G z) := by
  let f : G → (orbit G x × orbit G y) × orbit G z := fun g =>
    ((⟨g • x, mem_orbit_iff.mpr ⟨g, rfl⟩⟩,
      ⟨g • y, mem_orbit_iff.mpr ⟨g, rfl⟩⟩),
      ⟨g • z, mem_orbit_iff.mpr ⟨g, rfl⟩⟩)
  have hi : Function.Injective f := by
    intro a b hab
    have hx : a • x = b • x := congrArg (fun t => t.1.1.val) hab
    have hy : a • y = b • y := congrArg (fun t => t.1.2.val) hab
    have hz : a • z = b • z := congrArg (fun t => t.2.val) hab
    have he : b⁻¹ * a = 1 := hfree _
      (by rw [mul_smul, hx, inv_smul_smul])
      (by rw [mul_smul, hy, inv_smul_smul])
      (by rw [mul_smul, hz, inv_smul_smul])
    exact (inv_mul_eq_one.mp he).symm
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hi

end FiveTransitive.AbelianOrbitEvaluation

end CFSG
