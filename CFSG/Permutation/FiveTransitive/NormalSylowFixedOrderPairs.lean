module

public import CFSG.Permutation.FiveTransitive.SmallNormalFourImage
public import CFSG.Permutation.FiveTransitive.NormalSylowInternalImage
public import CFSG.Permutation.FiveTransitive.NormalSylowFixedDegreeSeven

public section

namespace CFSG

namespace FiveTransitive.NormalSylowFixedOrderPairs
open MulAction GenericSylowFixedAction

theorem degree_order_pairs
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h5 : IsMultiplyPretransitive G X 5)
    (N : Subgroup G) [N.Normal] (hN4 : IsMultiplyPretransitive N X 4)
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup N s)) :
    let F := sylowFixedPoints N X s S
    let L := (MulAction.toPermHom (sylowNormalizer N X s S) F).range
    (Nat.card F = 4 ∧ Nat.card L = 24) ∨
      (Nat.card F = 5 ∧ Nat.card L = 120) ∨
      (Nat.card F = 6 ∧ Nat.card L = 360) ∨
      (Nat.card F = 7 ∧ Nat.card L = 2520) := by
  classical
  dsimp only
  let F := sylowFixedPoints N X s S
  let _ : Fintype F := Fintype.ofFinite F
  let A := sylowNormalizer N X s S
  let L := (MulAction.toPermHom A F).range
  obtain ⟨J, hLJ, hnormal, hJ5⟩ :=
    NormalSylowInternalImage.exists_five_transitive_normal_overgroup G X h5 N s hs S
  let _ : (L.subgroupOf J).Normal := hnormal
  have hL4 : IsMultiplyPretransitive L F 4 :=
    FiveTransitive.isMultiplyPretransitive_range_toPermHom A F 4
      (NormalSylowFixedDegree.internal_normalizer_four_transitive N X hN4 s hs S)
  have hlower : 4 ≤ Nat.card F := by
    simpa only [hs] using base_card_le_fixed_degree N X s S
  have hupper : Nat.card F ≤ 7 := by
    have h := NormalSylowFixedDegreeSeven.fixed_degree_le_seven G X h5 N hN4 s hs S
    rwa [NormalSylowFixedDegree.normal_fixedPoints_eq_internal] at h
  let sF : Set F := {x | (x : X) ∈ s}
  have hbase : s ⊆ (F : Set X) := base_subset_fixedPoints N X s S
  let e : s ≃ sF :=
    { toFun := fun x => ⟨⟨x.val, hbase x.property⟩, x.property⟩
      invFun := fun x => ⟨x.val.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsF : sF.ncard = 4 := by
    rw [← Nat.card_coe_set_eq, Nat.card_congr e.symm, Nat.card_coe_set_eq, hs]
  have hodd := prime_not_dvd_fixedAction_stabilizer_card N X s S
  have h := SmallNormalFourImage.degree_order_pairs F J L hLJ
    (by simpa only [Nat.card_eq_fintype_card] using hlower)
    (by simpa only [Nat.card_eq_fintype_card] using hupper) hJ5 hL4 sF hsF hodd
  simpa only [Nat.card_eq_fintype_card] using h

end FiveTransitive.NormalSylowFixedOrderPairs

end CFSG
