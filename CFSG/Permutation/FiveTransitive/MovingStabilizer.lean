module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

namespace FiveTransitive.MovingStabilizer

open MulAction SubMulAction

private theorem two_transitive
    {G X : Type*} [Group G] [MulAction G X] (a : X)
    (hmove : ∃ g : G, g • a ≠ a)
    (hstab : IsPretransitive (stabilizer G a) (ofStabilizer G a)) :
    IsMultiplyPretransitive G X 2 := by
  let _ := hstab
  obtain ⟨g,hg⟩ := hmove
  have hreach (x : X) : ∃ u : G, u • a = x := by
    by_cases hx : x = a
    · subst x
      exact ⟨1,one_smul G a⟩
    · let b : ofStabilizer G a := ⟨g • a,hg⟩
      let y : ofStabilizer G a := ⟨x,hx⟩
      obtain ⟨u,hu⟩ := exists_smul_eq (stabilizer G a) b y
      refine ⟨u.val * g,?_⟩
      have hv := congrArg (fun t : ofStabilizer G a => t.val) hu
      change u.val • (g • a) = x at hv
      simpa only [mul_smul] using hv
  let _ : IsPretransitive G X := ⟨by
    intro x y
    obtain ⟨u,hu⟩ := hreach x
    obtain ⟨v,hv⟩ := hreach y
    refine ⟨v * u⁻¹,?_⟩
    rw [mul_smul,←hu,inv_smul_smul,hv]⟩
  exact (ofStabilizer.isMultiplyPretransitive (a := a)).mpr
    (is_one_pretransitive_iff.mpr hstab)

theorem fixer_complement_two_transitive
    {G X : Type*} [Group G] [MulAction G X] (s : Set X) (a : X) (ha : a ∉ s)
    (hmove : ∃ g : fixingSubgroup G s, (g : G) • a ≠ a)
    (htrans : IsPretransitive (fixingSubgroup G (insert a s))
      (ofFixingSubgroup G (insert a s))) :
    IsMultiplyPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s) 2 := by
  let _ := htrans
  let z : ofFixingSubgroup G s := ⟨a,ha⟩
  apply two_transitive z
  · obtain ⟨g,hg⟩ := hmove
    exact ⟨g,fun h => hg (congrArg Subtype.val h)⟩
  · constructor
    intro x y
    have hx : x.val.val ∉ insert a s := by
      intro h
      rcases h with h | h
      · exact x.property (Subtype.ext h)
      · exact x.val.property h
    have hy : y.val.val ∉ insert a s := by
      intro h
      rcases h with h | h
      · exact y.property (Subtype.ext h)
      · exact y.val.property h
    obtain ⟨g,hg⟩ := exists_smul_eq (fixingSubgroup G (insert a s))
      (⟨x.val.val,hx⟩ : ofFixingSubgroup G (insert a s)) ⟨y.val.val,hy⟩
    let u : fixingSubgroup G s := ⟨g.val,by
      rw [mem_fixingSubgroup_iff]
      intro t ht
      exact (mem_fixingSubgroup_iff G).mp g.property t (Set.mem_insert_of_mem a ht)⟩
    have hu : u ∈ stabilizer (fixingSubgroup G s) z := by
      apply Subtype.ext
      exact (mem_fixingSubgroup_iff G).mp g.property a (Set.mem_insert a s)
    refine ⟨⟨u,hu⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (g : G) • x.val.val = y.val.val
    exact congrArg (fun t : ofFixingSubgroup G (insert a s) => t.val) hg

end FiveTransitive.MovingStabilizer

end CFSG
