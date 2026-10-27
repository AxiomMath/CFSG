module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

variable {G X : Type*} [Group G] [MulAction G X]

theorem orbit_sup_eq_of_smul_mem {Y S : Subgroup G} {x : X}
    (hS : ∀ s ∈ S, ∀ y ∈ MulAction.orbit Y x, s • y ∈ MulAction.orbit Y x) :
    MulAction.orbit (Y ⊔ S : Subgroup G) x = MulAction.orbit Y x := by
  let T : Subgroup G :=
    { carrier := {g | ∀ y ∈ MulAction.orbit Y x,
        g • y ∈ MulAction.orbit Y x ∧ g⁻¹ • y ∈ MulAction.orbit Y x}
      mul_mem' := by
        intro a b ha hb y hy
        exact ⟨by rw [mul_smul]; exact (ha _ (hb _ hy).1).1,
          by rw [mul_inv_rev, mul_smul]; exact (hb _ (ha _ hy).2).2⟩
      one_mem' := by
        intro y hy
        simpa using And.intro hy hy
      inv_mem' := by
        intro a ha y hy
        exact ⟨(ha y hy).2, by rw [inv_inv]; exact (ha y hy).1⟩ }
  have hmove : ∀ g ∈ Y, ∀ y ∈ MulAction.orbit Y x, g • y ∈ MulAction.orbit Y x := by
    intro g hg y hy
    obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    exact MulAction.mem_orbit_iff.mpr ⟨⟨g, hg⟩ * h, mul_smul _ _ _⟩
  have hYT : Y ≤ T := by
    intro g hg y hy
    exact ⟨hmove g hg y hy, hmove g⁻¹ (Y.inv_mem hg) y hy⟩
  have hST : S ≤ T := by
    intro s hs y hy
    exact ⟨hS s hs y hy, hS s⁻¹ (S.inv_mem hs) y hy⟩
  have hsup : ∀ g ∈ Y ⊔ S, ∀ y ∈ MulAction.orbit Y x,
      g • y ∈ MulAction.orbit Y x := fun g hg y hy => ((sup_le hYT hST) hg y hy).1
  apply Set.Subset.antisymm
  · rintro _ ⟨g, rfl⟩
    exact hsup g g.2 x (MulAction.mem_orbit_self x)
  · rintro _ ⟨h, rfl⟩
    exact ⟨⟨h, Subgroup.mem_sup_left h.2⟩, rfl⟩

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving
