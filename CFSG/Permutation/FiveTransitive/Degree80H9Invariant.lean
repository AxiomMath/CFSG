module

public import CFSG.Permutation.FiveTransitive.H9OrbitAction
public import CFSG.Permutation.FiveTransitive.OrderNineFixedCount
public import CFSG.Permutation.FiveTransitive.Degree80H9Numeric
public import CFSG.Permutation.FiveTransitive.Degree80TwoTwelveOrbitMass
public import CFSG.Permutation.FiveTransitive.Degree52TwoOrbitPreserved

public section

namespace CFSG

namespace FiveTransitive.Degree80H9Invariant
open MulAction

theorem orbit_cases
    {G H X : Type*} [Group G] [Group H] [Finite H] [Fintype X] [MulAction G X]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hX : Nat.card X = 80)
    (i : H →* Subgroup.normalizer (Q : Set G)) (hH : Nat.card H = 9)
    (E : Set X) (hE : E.ncard = 2)
    (hEout : ∀ x ∈ E, x ∉ fixedPoints Q X)
    (hEfix : ∀ h : H, ∀ x ∈ E, (i h).val • x = x)
    (hexact : ∀ h : H, h ≠ 1 → ∀ x : X,
      x ∉ fixedPoints Q X → ((i h).val • x = x ↔ x ∈ E))
    (O : orbitRel.Quotient Q X) (x : X) (hx : x ∈ E) (hxO : x ∈ O.orbit) :
    (Nat.card O.orbit = 2 ∧ (E ∩ O.orbit).ncard = 2) ∨
      (Nat.card O.orbit = 64 ∧ (E ∩ O.orbit).ncard = 1) := by
  classical
  have hO : Nat.card O.orbit ≠ 1 := by
    intro hone
    have he := orbitRel.Quotient.mem_orbit.mp hxO
    apply hEout x hx
    apply mem_fixedPoints_iff_card_orbit_eq_one.mpr
    rw [← Nat.card_eq_fintype_card,← orbitRel.Quotient.orbit_mk,he,hone]
  have hInv := H9OrbitAction.invariant_of_fixed_point Q i O x hxO (fun h => hEfix h x hx)
  let rho := H9OrbitAction.toPermHom Q i O hInv
  let _ : MulAction H O.orbit := MulAction.compHom _ rho
  have hcount (h : H) (hh : h ≠ 1) :
      Nat.card (fixedBy O.orbit h) = (E ∩ O.orbit).ncard := by
    let e : fixedBy O.orbit h ≃ ↥(E ∩ O.orbit) :=
      { toFun := fun y => ⟨y.val.val,
          (hexact h hh y.val.val
            (Degree52TwoOrbitPreserved.not_fixed_of_mem Q O hO _ y.val.property)).mp
            (congrArg Subtype.val y.property), y.val.property⟩
        invFun := fun y => ⟨⟨y.val,y.property.2⟩,Subtype.ext
          ((hexact h hh y.val (hEout y.val y.property.1)).mpr y.property.1)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e,Nat.card_coe_set_eq]
  have hm := OrderNineFixedCount.constant_congruence (Y := O.orbit) hH
    (E ∩ O.orbit).ncard hcount
  have hlo : 1 ≤ (E ∩ O.orbit).ncard := by
    have hn : (E ∩ O.orbit).Nonempty := ⟨x,hx,hxO⟩
    exact Nat.succ_le_of_lt ((Set.ncard_pos (Set.toFinite _)).mpr hn)
  have hhi : (E ∩ O.orbit).ncard ≤ 2 := by
    simpa only [hE] using Set.ncard_le_ncard (Set.inter_subset_left (s := E) (t := O.orbit))
  have hc := Degree80TwoTwelveOrbitMass.orbit_card_cases hX.le Q hQ O
  exact Degree80H9Numeric.invariant_cases _ _ (by omega) hlo hhi hm

end FiveTransitive.Degree80H9Invariant

end CFSG
