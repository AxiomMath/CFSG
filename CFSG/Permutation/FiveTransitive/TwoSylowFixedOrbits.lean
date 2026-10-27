module

public import CFSG.Permutation.FiveTransitive.SylowThreeFixedOrbits

public section

namespace CFSG

namespace FiveTransitive.TwoSylowFixedOrbits

open MulAction

variable {H X : Type*} [Group H] [Finite H] [MulAction H X] [Finite X]

private def fixedOrbitEquiv (S : Subgroup H) (u : X) :
    fixedPoints S (SylowThreeFixedOrbits.orbitAction S u) ≃
      ↥(orbit H u ∩ fixedPoints S X) where
  toFun x := ⟨x.val.val, x.val.property, by
    rw [mem_fixedPoints]
    intro q
    exact congrArg Subtype.val (mem_fixedPoints.mp x.property q)⟩
  invFun x := ⟨⟨x.val,x.property.1⟩, by
    rw [mem_fixedPoints]
    intro q
    apply Subtype.ext
    exact mem_fixedPoints.mp x.property.2 q⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Finite H] [Finite X] in
theorem orbit_disjoint_fixed (u : X) (hu : u ∉ fixedPoints H X) :
    Disjoint (orbit H u) (fixedPoints H X) := by
  rw [Set.disjoint_left]
  intro x hx hf
  obtain ⟨h,rfl⟩ := mem_orbit_iff.mp hx
  have he : h • u = u := by
    have ht := mem_fixedPoints.mp hf h⁻¹
    simpa only [inv_smul_smul] using ht.symm
  exact hu (he ▸ hf)

theorem two_odd_distinct (S : Sylow 2 H) (s : Set X) (u v : X)
    (hH : fixedPoints H X = s) (hS : fixedPoints S X = s ∪ {u,v})
    (hu : u ∉ s) (_hv : v ∉ s) (huv : u ≠ v) :
    (¬ 2 ∣ Nat.card (orbit H u)) ∧ (¬ 2 ∣ Nat.card (orbit H v)) ∧
      v ∉ orbit H u := by
  classical
  have huf : u ∈ fixedPoints S X := by rw [hS]; simp
  have hvf : v ∈ fixedPoints S X := by rw [hS]; simp
  have hou := SylowThreeFixedOrbits.odd_orbit_of_sylow_fixed u S huf
  have hov := SylowThreeFixedOrbits.odd_orbit_of_sylow_fixed v S hvf
  refine ⟨hou,hov,?_⟩
  intro hvo
  have hd := orbit_disjoint_fixed u (by rwa [hH])
  have he : orbit H u ∩ fixedPoints S X = {u,v} := by
    ext x
    constructor
    · rintro ⟨hxo,hxf⟩
      rw [hS] at hxf
      rcases hxf with hxs | hxuv
      · exact False.elim (Set.disjoint_left.mp hd hxo (hH ▸ hxs))
      · exact hxuv
    · intro hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact ⟨mem_orbit_self _,huf⟩
      · have hxv := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨hvo,hvf⟩
  have hc : Nat.card (fixedPoints S (SylowThreeFixedOrbits.orbitAction (S : Subgroup H) u)) = 2 := by
    rw [Nat.card_congr (fixedOrbitEquiv (S : Subgroup H) u), Nat.card_coe_set_eq, he]
    simp [huv]
  have hm := S.isPGroup'.card_modEq_card_fixedPoints
    (SylowThreeFixedOrbits.orbitAction (S : Subgroup H) u)
  change Nat.card (orbit H u) % 2 = _ at hm
  rw [hc] at hm
  exact hou (Nat.dvd_of_mod_eq_zero hm)

omit [Finite H] [Finite X] in
theorem fixed_inter_orbit (S : Sylow 2 H) (s : Set X) (u v : X)
    (hH : fixedPoints H X = s) (hS : fixedPoints S X = s ∪ {u,v})
    (hu : u ∉ s) (hvu : v ∉ orbit H u) :
    orbit H u ∩ fixedPoints S X = {u} := by
  have hd := orbit_disjoint_fixed u (by rwa [hH])
  ext x
  constructor
  · rintro ⟨hxo,hxf⟩
    rw [hS] at hxf
    rcases hxf with hxs | hxuv
    · exact False.elim (Set.disjoint_left.mp hd hxo (hH ▸ hxs))
    · rcases Set.mem_insert_iff.mp hxuv with rfl | hxv
      · exact Set.mem_singleton _
      · exact False.elim (hvu ((Set.mem_singleton_iff.mp hxv) ▸ hxo))
  · rintro rfl
    exact ⟨mem_orbit_self _,by rw [hS]; simp⟩

end FiveTransitive.TwoSylowFixedOrbits

end CFSG
