module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

public section

namespace CFSG

namespace FiveTransitive.SylowFullFixedSet

open MulAction

private theorem exists_intermediate
    {G : Type*} [Group G] {p : ℕ} (H K : Subgroup G) (hKH : K ≤ H)
    (S : Sylow p H) (hSK : (S : Subgroup H).map H.subtype ≤ K) :
    ∃ T : Sylow p K, (T : Subgroup K).map K.subtype = (S : Subgroup H).map H.subtype := by
  let i : K →* H := Subgroup.inclusion hKH
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : H => z.val) h)
  have hr : (S : Subgroup H) ≤ i.range := by
    intro s hs
    exact ⟨⟨s.val, hSK ⟨s, hs, rfl⟩⟩, rfl⟩
  let T := S.comapOfInjective i hi hr
  refine ⟨T, ?_⟩
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨i k, hk, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s.val, hSK ⟨s, hs, rfl⟩⟩, hs, rfl⟩

theorem exists_full_fixer
    {G X : Type*} [Group G] [MulAction G X] {p : ℕ}
    (s : Set X) (T : Sylow p (fixingSubgroup G s))
    (Q : Subgroup G) (hT : (T : Subgroup (fixingSubgroup G s)).map
      (fixingSubgroup G s).subtype = Q) :
    ∃ S : Sylow p (fixingSubgroup G (fixedPoints Q X)),
      (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
        (fixingSubgroup G (fixedPoints Q X)).subtype = Q := by
  have hs : s ⊆ fixedPoints Q X := by
    intro x hx q
    have hq : q.val ∈ (T : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype := by
      rw [hT]
      exact q.property
    obtain ⟨t, ht, he⟩ := hq
    change (t : G) = q.val at he
    change q.val • x = x
    rw [←he]
    exact (mem_fixingSubgroup_iff G).mp t.property x hx
  have hKH : fixingSubgroup G (fixedPoints Q X) ≤ fixingSubgroup G s := by
    intro g hg
    exact (mem_fixingSubgroup_iff G).mpr fun x hx =>
      (mem_fixingSubgroup_iff G).mp hg x (hs hx)
  have hQK : Q ≤ fixingSubgroup G (fixedPoints Q X) := by
    intro q hq
    exact (mem_fixingSubgroup_iff G).mpr fun x hx => mem_fixedPoints.mp hx ⟨q, hq⟩
  obtain ⟨S, hS⟩ := exists_intermediate _ _ hKH T (by rw [hT]; exact hQK)
  exact ⟨S, hS.trans hT⟩

end FiveTransitive.SylowFullFixedSet

end CFSG
