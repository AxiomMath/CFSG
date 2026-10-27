module

public import CFSG.Permutation.FiveTransitive.OddNormalSylowTransitive
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

public section

namespace CFSG

namespace FiveTransitive.OddNormalFixerTransitive

open MulAction SubMulAction

theorem isPretransitive_of_fixed_points
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (N : Subgroup G) [N.Normal] (s : Set X)
    (htrans : IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s))
    (S : Sylow 2 (fixingSubgroup N s))
    (hodd : Odd (Nat.card X - s.ncard))
    (hconnect : ∀ u v : X, u ∉ s → v ∉ s →
      (∀ q : S, q • u = u) → (∀ q : S, q • v = v) →
      ∃ n : fixingSubgroup N s, n • u = v) :
    IsPretransitive (fixingSubgroup N s) (ofFixingSubgroup N s) := by
  let K := fixingSubgroup G s
  let H : Subgroup K := N.comap K.subtype
  let Y := ofFixingSubgroup G s
  let _ : IsPretransitive K Y := htrans
  let e : fixingSubgroup N s ≃* H :=
    { toFun := fun q => ⟨⟨q.val.val, by
        rw [mem_fixingSubgroup_iff]
        exact (mem_fixingSubgroup_iff N).mp q.property⟩, q.val.property⟩
      invFun := fun q => ⟨⟨q.val.val, q.property⟩, by
        rw [mem_fixingSubgroup_iff]
        exact (mem_fixingSubgroup_iff G).mp q.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let T : Sylow 2 H := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S
  have hoddY : Odd (Nat.card Y) := by
    change Odd (Nat.card (sᶜ : Set X))
    rw [Nat.card_coe_set_eq, Set.ncard_compl]
    exact hodd
  have hH : IsPretransitive H Y :=
    OddNormalSylowTransitive.isPretransitive_of_fixed_points K Y H T hoddY (by
      intro u v
      have hfix (w : fixedPoints T Y) (q : S) : q • w.val.val = w.val.val := by
        have hq : e q.val ∈ T := by
          exact Subgroup.mem_map_of_mem e.toMonoidHom q.property
        exact congrArg Subtype.val (mem_fixedPoints.mp w.property ⟨e q.val, hq⟩)
      obtain ⟨n, hn⟩ := hconnect u.val.val v.val.val u.val.property v.val.property
        (hfix u) (hfix v)
      exact ⟨e n, Subtype.ext hn⟩)
  constructor
  intro u v
  obtain ⟨n, hn⟩ := hH.exists_smul_eq (⟨u.val, u.property⟩ : Y) ⟨v.val, v.property⟩
  exact ⟨e.symm n, Subtype.ext (congrArg Subtype.val hn)⟩

end FiveTransitive.OddNormalFixerTransitive

end CFSG
