module

public import CFSG.Permutation.FiveTransitive.MaximalSylowPointStabilizer
public import CFSG.Permutation.FiveTransitive.MinimalOrbitStabilizer
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

public section

namespace CFSG

namespace FiveTransitive.MinimalOrbitFixerSylow

open MulAction

private def insertFixerEquiv (G X : Type*) [Group G] [MulAction G X]
    (s : Set X) (x : X) :
    stabilizer (fixingSubgroup G s) x ≃* fixingSubgroup G (insert x s) where
  toFun g := ⟨g.val.val, by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    rcases hy with rfl | hy
    · exact g.property
    · exact (mem_fixingSubgroup_iff G).mp g.val.property y hy⟩
  invFun g := ⟨⟨g.val, (mem_fixingSubgroup_iff G).mpr fun y hy =>
      (mem_fixingSubgroup_iff G).mp g.property y (Set.mem_insert_of_mem x hy)⟩,
    (mem_fixingSubgroup_iff G).mp g.property x (Set.mem_insert x s)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem sylow_of_maximal_stabilizer
    (G X : Type*) [Group G] [Finite G] [MulAction G X]
    (s : Set X) {p : ℕ} [Fact p.Prime] (S : Sylow p (fixingSubgroup G s))
    (x : X) (hx : x ∉ s)
    (hmax : ∀ y : X, y ∉ s → Nat.card (stabilizer S y) ≤ Nat.card (stabilizer S x)) :
    ∃ T : Sylow p (fixingSubgroup G (insert x s)),
      (T : Subgroup (fixingSubgroup G (insert x s))).map
          (fixingSubgroup G (insert x s)).subtype =
        (stabilizer S x).map ((fixingSubgroup G s).subtype.comp (S : Subgroup _).subtype) := by
  let K := fixingSubgroup G s
  have hmax' (k : K) : Nat.card (stabilizer S (k • x)) ≤ Nat.card (stabilizer S x) := by
    apply hmax
    intro hkx
    have hfixed : k⁻¹ • (k • x) = k • x := (mem_fixingSubgroup_iff G).mp k⁻¹.property (k • x) hkx
    rw [inv_smul_smul] at hfixed
    exact hx (hfixed ▸ hkx)
  obtain ⟨R,hR⟩ := MaximalSylowPointStabilizer.exists_sylow_with_same_image_of_orbit_max
    K X S x hmax'
  let E := insertFixerEquiv G X s x
  let T := Sylow.mapSurjective (f := E.toMonoidHom) E.surjective R
  refine ⟨T, ?_⟩
  have he : (fixingSubgroup G (insert x s)).subtype.comp E.toMonoidHom =
      K.subtype.comp (stabilizer K x).subtype := rfl
  change ((R : Subgroup (stabilizer K x)).map E.toMonoidHom).map
    (fixingSubgroup G (insert x s)).subtype = _
  rw [Subgroup.map_map,he,← Subgroup.map_map,hR,Subgroup.map_map]

theorem sylow_of_minimal_orbit
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (s : Set X) {p : ℕ} [Fact p.Prime] (S : Sylow p (fixingSubgroup G s))
    (hfixed : fixedPoints S X = s) (x : X) (hx : x ∉ s)
    (hmin : ∀ y : X, y ∉ fixedPoints S X → Nat.card (orbit S x) ≤ Nat.card (orbit S y)) :
    ∃ T : Sylow p (fixingSubgroup G (insert x s)),
      (T : Subgroup (fixingSubgroup G (insert x s))).map
          (fixingSubgroup G (insert x s)).subtype =
        (stabilizer S x).map ((fixingSubgroup G s).subtype.comp (S : Subgroup _).subtype) := by
  apply sylow_of_maximal_stabilizer G X s S x hx
  intro y hy
  have hxcard := MinimalOrbitStabilizer.nat_card_orbit_mul_stabilizer S X x
  have hycard := MinimalOrbitStabilizer.nat_card_orbit_mul_stabilizer S X y
  have hh := Nat.mul_le_mul_right (Nat.card (stabilizer S y)) (hmin y (by rwa [hfixed]))
  rw [hycard,←hxcard] at hh
  have : Nonempty (orbit S x) := ⟨⟨x,mem_orbit_self x⟩⟩
  exact Nat.le_of_mul_le_mul_left hh Nat.card_pos

end FiveTransitive.MinimalOrbitFixerSylow

end CFSG
