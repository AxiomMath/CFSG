module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Actions

public section

namespace CFSG

open scoped commutatorElement

namespace FiveTransitive.AbelianOrbitCommutator

open MulAction

variable {G Y : Type*} [Group G] [MulAction G Y]

private theorem commute_at_orbit (Q : Subgroup G) [IsMulCommutative Q]
    (a b : G) (ha : a ∈ Subgroup.centralizer (Q : Set G))
    (hb : b ∈ Subgroup.centralizer (Q : Set G)) (y : Y)
    (hay : a • y ∈ orbit Q y) (hby : b • y ∈ orbit Q y) :
    a • (b • y) = b • (a • y) := by
  obtain ⟨q, hq⟩ := mem_orbit_iff.mp hay
  obtain ⟨r, hr⟩ := mem_orbit_iff.mp hby
  have har : a * (r : G) = (r : G) * a :=
    (Subgroup.mem_centralizer_iff.mp ha r r.property).symm
  have hbq : b * (q : G) = (q : G) * b :=
    (Subgroup.mem_centralizer_iff.mp hb q q.property).symm
  calc
    a • (b • y) = a • (r • y) := by rw [hr]
    _ = r • (a • y) := by change a • ((r : G) • y) = (r : G) • (a • y); rw [← mul_smul, har, mul_smul]
    _ = r • (q • y) := by rw [hq]
    _ = q • (r • y) := by rw [← mul_smul, ← mul_smul, (isMulCommutative_iff.mp inferInstance r q)]
    _ = q • (b • y) := by rw [hr]
    _ = b • (q • y) := by change (q : G) • (b • y) = b • ((q : G) • y); rw [← mul_smul, ← hbq, mul_smul]
    _ = b • (a • y) := by rw [hq]

private theorem commutator_le_fixer_of_commute (K : Subgroup G) (s : Set Y)
    (hstable : ∀ a ∈ K, ∀ y ∈ s, a • y ∈ s)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, ∀ y ∈ s, a • (b • y) = b • (a • y)) :
    ⁅K, K⁆ ≤ fixingSubgroup G s := by
  apply Subgroup.commutator_le.mpr
  intro a ha b hb
  rw [mem_fixingSubgroup_iff]
  intro y hy
  have hz : a⁻¹ • (b⁻¹ • y) ∈ s :=
    hstable a⁻¹ (K.inv_mem ha) _ (hstable b⁻¹ (K.inv_mem hb) y hy)
  simp only [commutatorElement_def, mul_smul]
  rw [hcomm a ha b hb _ hz]
  simp only [smul_inv_smul]

theorem commutator_fixes_orbit (Q K : Subgroup G) [IsMulCommutative Q]
    (hcentral : K ≤ Subgroup.centralizer (Q : Set G))
    (O : orbitRel.Quotient Q Y)
    (hpreserve : ∀ a ∈ K, ∀ y : Y, (Quotient.mk'' y : orbitRel.Quotient Q Y) = O →
      (Quotient.mk'' (a • y) : orbitRel.Quotient Q Y) = O) :
    ∀ a ∈ ⁅K, K⁆, ∀ y : Y, (Quotient.mk'' y : orbitRel.Quotient Q Y) = O → a • y = y := by
  have hfix : ⁅K, K⁆ ≤ fixingSubgroup G
      {y : Y | (Quotient.mk'' y : orbitRel.Quotient Q Y) = O} := by
    apply commutator_le_fixer_of_commute K _ hpreserve
    intro a ha b hb y hy
    apply commute_at_orbit Q a b (hcentral ha) (hcentral hb) y
    · exact Quotient.exact ((hpreserve a ha y hy).trans hy.symm)
    · exact Quotient.exact ((hpreserve b hb y hy).trans hy.symm)
  intro a ha y hy
  exact (mem_fixingSubgroup_iff G).mp (hfix ha) y hy

end FiveTransitive.AbelianOrbitCommutator

end CFSG
