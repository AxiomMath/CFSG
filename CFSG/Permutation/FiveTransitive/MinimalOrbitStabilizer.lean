module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Finset.Max

public section

namespace CFSG

namespace FiveTransitive.MinimalOrbitStabilizer

open MulAction

theorem nat_card_orbit_mul_stabilizer
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X] (x : X) :
    Nat.card (orbit G x) * Nat.card (stabilizer G x) = Nat.card G := by
  classical
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite (orbit G x)
  let _ := Fintype.ofFinite (stabilizer G x)
  simpa only [Nat.card_eq_fintype_card] using card_orbit_mul_card_stabilizer_eq_card_group G x

theorem stabilizer_eq_of_minimal_orbit
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (t : X) (hmin : ∀ y : X, y ∉ fixedPoints G X → Nat.card (orbit G t) ≤ Nat.card (orbit G y))
    (Q : Subgroup G) (hQcard : Nat.card Q = Nat.card (stabilizer G t))
    (x : X) (hxQ : x ∈ fixedPoints Q X) (hx : x ∉ fixedPoints G X) :
    stabilizer G x = Q := by
  have hle : Q ≤ stabilizer G x := by
    intro q hq
    exact mem_fixedPoints.mp hxQ ⟨q,hq⟩
  have htcard := nat_card_orbit_mul_stabilizer G X t
  have hxcard := nat_card_orbit_mul_stabilizer G X x
  have h := Nat.mul_le_mul_right (Nat.card (stabilizer G x)) (hmin x hx)
  rw [hxcard,←htcard,←hQcard] at h
  have : Nonempty (orbit G t) := ⟨⟨t,mem_orbit_self t⟩⟩
  exact (Subgroup.eq_of_le_of_card_ge hle (Nat.le_of_mul_le_mul_left h Nat.card_pos)).symm

theorem fixedPoints_subset_stabilizer_fixedPoints
    (G X : Type*) [Group G] [MulAction G X] (t : X) :
    fixedPoints G X ⊆ fixedPoints (stabilizer G t) X := by
  intro x hx
  rw [mem_fixedPoints]
  intro q
  exact mem_fixedPoints.mp hx (q : G)

theorem self_mem_stabilizer_fixedPoints
    (G X : Type*) [Group G] [MulAction G X] (t : X) :
    t ∈ fixedPoints (stabilizer G t) X := by
  rw [mem_fixedPoints]
  intro q
  exact q.property

theorem exists_minimal_orbit_stabilizer
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (hmove : ∃ (g : G) (x : X), g • x ≠ x) :
    ∃ t : X, t ∉ fixedPoints G X ∧
      (∀ y : X, y ∉ fixedPoints G X → Nat.card (orbit G t) ≤ Nat.card (orbit G y)) ∧
      stabilizer G t ≠ ⊤ ∧ fixedPoints G X ⊂ fixedPoints (stabilizer G t) X := by
  classical
  let _ := Fintype.ofFinite X
  let A := Finset.univ.filter (fun x : X => x ∉ fixedPoints G X)
  obtain ⟨g,x,hgx⟩ := hmove
  have hx : x ∉ fixedPoints G X := fun hx => hgx (mem_fixedPoints.mp hx g)
  have hA : A.Nonempty := ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ x,hx⟩⟩
  obtain ⟨t,ht,hminimal⟩ := Finset.exists_min_image A (fun x=>Nat.card (orbit G x)) hA
  have htfix : t ∉ fixedPoints G X := (Finset.mem_filter.mp ht).2
  have hmin : ∀ y : X, y ∉ fixedPoints G X → Nat.card (orbit G t) ≤ Nat.card (orbit G y) := by
    intro y hy
    exact hminimal y (Finset.mem_filter.mpr ⟨Finset.mem_univ y,hy⟩)
  have hproper : stabilizer G t ≠ ⊤ := by
    intro he
    apply htfix
    rw [mem_fixedPoints]
    intro a
    have hmem : a ∈ stabilizer G t := by rw [he]; trivial
    exact hmem
  refine ⟨t,htfix,hmin,hproper,?_⟩
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨fixedPoints_subset_stabilizer_fixedPoints G X t,?_⟩
  intro he
  exact htfix (he.symm ▸ self_mem_stabilizer_fixedPoints G X t)

end FiveTransitive.MinimalOrbitStabilizer

end CFSG
